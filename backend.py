"""
Tugle — servidor do jogo diário, com catálogo próprio de músicas.

Em vez de ir buscar músicas à Deezer e esquecê-las no dia seguinte, este
servidor mantém uma tabela `faixas` que cresce com o tempo: cada dia que
precisa de mais candidatos explora mais alguns artistas, guarda o que
encontra (título, artista, capa, áudio, género, década) e evita repetir uma
faixa usada nos últimos 45 dias.

Instalar e correr localmente:
    python3.12 -m venv .venv && source .venv/bin/activate
    pip install -r requirements.txt
    fastapi dev backend.py

Produção (systemd, Render, etc.):
    uvicorn backend:app --host 0.0.0.0 --port 8000
"""

from __future__ import annotations

import datetime as dt
import os
import random
import re
import secrets
import time
import unicodedata
from collections import defaultdict
from contextlib import asynccontextmanager
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit
from uuid import uuid4
from zoneinfo import ZoneInfo

import bcrypt
import httpx
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from apscheduler.triggers.cron import CronTrigger
from fastapi import Depends, FastAPI, Header, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, RedirectResponse, Response
from pydantic import BaseModel
from sqlalchemy import Integer, String, select
from sqlalchemy import JSON
from sqlalchemy.ext.asyncio import async_sessionmaker, create_async_engine
from sqlalchemy.orm import DeclarativeBase, Mapped, mapped_column

LISBOA = ZoneInfo("Europe/Lisbon")
DEEZER = "https://api.deezer.com"
def preparar_url_bd(url: str) -> tuple[str, dict]:
    """Aceita a morada tal como os serviços de Postgres a dão (ex.: Neon,
    Supabase) e ajusta-a para o que o SQLAlchemy assíncrono precisa:
    driver 'asyncpg' explícito, e SSL passado corretamente em vez de na
    query string (onde o asyncpg às vezes não o percebe bem)."""
    if url.startswith("postgres://"):
        url = "postgresql+asyncpg://" + url[len("postgres://"):]
    elif url.startswith("postgresql://"):
        url = "postgresql+asyncpg://" + url[len("postgresql://"):]

    if "+asyncpg" not in url:
        return url, {}

    partes = urlsplit(url)
    query = dict(parse_qsl(partes.query))
    query.pop("sslmode", None)
    query.pop("ssl", None)
    query.pop("channel_binding", None)
    url_limpo = urlunsplit((partes.scheme, partes.netloc, partes.path, urlencode(query), partes.fragment))
    return url_limpo, {"ssl": "require"}


BASE_DE_DADOS, _connect_args = preparar_url_bd(
    os.environ.get("DATABASE_URL", "sqlite+aiosqlite:///tugle.db")
)
DIAS_ATE_REPETIR = 45      # uma faixa só volta a sair passado este tempo
TAMANHO_MINIMO_CATALOGO = 1000

# Datas festivas: se não houver faixas suficientes desse tema nesse dia,
# cai-se sozinho no catálogo normal — nunca bloqueia a geração do puzzle.
ARTISTAS_FADO = {
    "Amália Rodrigues", "Mariza", "Carminho", "Ana Moura",
    "Gisela João", "Cuca Roseta", "Raquel Tavares", "Sara Correia",
}
ARTISTAS_PIMBA = {
    "Quim Barreiros", "Tony Carreira", "Emanuel", "Ana Malhoa", "Marco Paulo",
}

# datas fixas: (mês, dia) -> (nome do tema, artistas)
DATAS_FESTIVAS_FIXAS: dict[tuple[int, int], tuple[str, set[str]]] = {
    (12, 24): ("Véspera de Natal", ARTISTAS_FADO),
    (12, 25): ("Natal", ARTISTAS_FADO),
    (1, 1): ("Ano Novo", ARTISTAS_PIMBA),
}


def calcular_pascoa(ano: int) -> dt.date:
    """Domingo de Páscoa desse ano (algoritmo de Meeus/Jones/Butcher)."""
    a = ano % 19
    b = ano // 100
    c = ano % 100
    d = b // 4
    e = b % 4
    f = (b + 8) // 25
    g = (b - f + 1) // 3
    h = (19 * a + b - d - g + 15) % 30
    i = c // 4
    k = c % 4
    l = (32 + 2 * e + 2 * i - h - k) % 7
    m = (a + 11 * h + 22 * l) // 451
    mes = (h + l - 7 * m + 114) // 31
    dia = ((h + l - 7 * m + 114) % 31) + 1
    return dt.date(ano, mes, dia)


def tema_do_dia(data: dt.date) -> tuple[str, set[str]] | None:
    fixa = DATAS_FESTIVAS_FIXAS.get((data.month, data.day))
    if fixa:
        return fixa
    if data == calcular_pascoa(data.year):
        return ("Páscoa", ARTISTAS_PIMBA)
    carnaval = calcular_pascoa(data.year) - dt.timedelta(days=47)
    if data == carnaval:
        return ("Carnaval", ARTISTAS_PIMBA)
    return None

CHAVE_ADMIN = os.environ.get("ADMIN_KEY", "")


async def exigir_chave_admin(x_admin_key: str | None = Header(None)) -> None:
    """Protege endpoints que alteram ou apagam dados (regenerar puzzle,
    limpar catálogo). Sem ADMIN_KEY configurada no servidor, estas rotas
    ficam sempre fechadas — falha em segurança, não em conveniência.
    A chave vai num cabeçalho (X-Admin-Key), não no URL — assim não fica
    gravada no histórico do browser nem nos logs de acesso do servidor."""
    if not CHAVE_ADMIN:
        raise HTTPException(500, "ADMIN_KEY não está configurada no servidor.")
    if x_admin_key != CHAVE_ADMIN:
        raise HTTPException(401, "Chave de administração inválida ou em falta (cabeçalho X-Admin-Key).")
ENTRADAS_POR_PUZZLE = 16


_PEDIDOS_POR_CHAVE: dict[str, list[float]] = defaultdict(list)


def limite_excedido(chave: str, maximo: int, janela_segundos: int) -> bool:
    """Sim/não: esta chave (ex.: 'personalizado:1.2.3.4') já fez pedidos
    a mais dentro da janela de tempo. Guarda tudo em memória — chega bem
    para um único processo como este; não sobrevive a reinícios, o que é
    aceitável para um limitador de abuso, não para nada crítico."""
    agora = time.time()
    historico = _PEDIDOS_POR_CHAVE[chave]
    while historico and historico[0] < agora - janela_segundos:
        historico.pop(0)
    if len(historico) >= maximo:
        return True
    historico.append(agora)
    return False


async def limitar_puzzle_stream(request: Request) -> None:
    ip = request.client.host if request.client else "desconhecido"
    if limite_excedido(f"stream:{ip}", maximo=20, janela_segundos=300):
        raise HTTPException(429, "Demasiados pedidos em pouco tempo. Espera um pouco antes de gerares outro jogo.")


async def limitar_jogador(request: Request) -> None:
    ip = request.client.host if request.client else "desconhecido"
    if limite_excedido(f"jogador:{ip}", maximo=30, janela_segundos=300):
        raise HTTPException(429, "Demasiados pedidos em pouco tempo.")


async def limitar_conta(request: Request) -> None:
    ip = request.client.host if request.client else "desconhecido"
    # mais apertado do que o limitador geral — são endpoints com password
    if limite_excedido(f"conta:{ip}", maximo=10, janela_segundos=300):
        raise HTTPException(429, "Demasiadas tentativas em pouco tempo. Espera uns minutos.")


async def limitar_progresso(request: Request) -> None:
    ip = request.client.host if request.client else "desconhecido"
    if limite_excedido(f"progresso:{ip}", maximo=60, janela_segundos=300):
        raise HTTPException(429, "Demasiados pedidos em pouco tempo.")


# A Deezer recorta os 30s de antevisão a começar algures na música, muitas
# vezes ainda em desvanecimento/intro. Saltar uns segundos costuma aproximar
# do refrão — não há forma de o garantir sem analisar o áudio a sério.
INICIO_EXCERTO_SEGUNDOS = 6

# ---------------------------------------------------------------- artistas

ARTISTAS = [
    # fado
    "Amália Rodrigues", "Mariza", "Carminho", "Ana Moura",
    "Gisela João", "Cuca Roseta", "Raquel Tavares", "Sara Correia",
    # rock e indie
    "Zeca Afonso", "Sérgio Godinho", "Rui Veloso",
    "Xutos & Pontapés", "GNR", "Ornatos Violeta",
    "Pedro Abrunhosa",
    "Capitão Fausto", "Toranja", "Delfins", "D'ZRT", "Anjos",
    # hip-hop, R&B, kizomba, trap
    "Da Weasel", "Slow J", "Plutónio", "Papillon", "Dino D'Santiago",
    "Mishlawi", "Bispo", "Boss AC", "Regula", "Piruka", "Expensive Soul",
    "Toy", "Mizzy Miles", "Nga", "Karetus", "The Gift",
    "Sara Tavares", "Julinho KSD", "Nenny", "Sam The Kid", "Valete",
    "Dealema", "Mundo Segundo", "ProfJam", "HMB", "Wet Bed Gang",
    "Buraka Som Sistema", "Calema", "Anselmo Ralph",
    "C4 Pedro", "Ivandro", "Agir",
    "T-Rex", "D.A.M.A", "Buba Espinho", "Chico da Tina", "GROGNation",
    "Nininho Vaz Maia", "Gama WNTD", "ATOA", "LON3R JOHNY", "Dama",
    "9 Miller", "Hollyhood", "Dillaz", "Richie Campbell",
    # pop
    "Salvador Sobral", "Bárbara Tinoco", "Diogo Piçarra",
    "Aurea", "Ana Bacalhau", "Miguel Araújo", "David Carreira",
    "Fernando Daniel", "Marisa Liz", "Cláudia Pascoal",
    "Iolanda", "Bárbara Bandeira", "Blaya", "Mafalda Veiga", "Rita Guerra",
    "Van Zee", "Carolina Deslandes", "MARO", "NAPA", "Vizinhos",
    "Soraia Ramos", "Pedro Mafama",
    # pimba (muito popular em Portugal, apesar de tudo)
    "Quim Barreiros", "Tony Carreira", "Emanuel", "Ana Malhoa",
    "Marco Paulo",
    # outros
    "Isak", "Zigarro", "Armando Teles",
]


ARTISTAS_INTERNACIONAIS = [
    # pop / r&b
    "Taylor Swift", "Ed Sheeran", "Adele", "Bruno Mars", "The Weeknd",
    "Beyoncé", "Drake", "Rihanna", "Dua Lipa", "Ariana Grande",
    "Billie Eilish", "Justin Bieber", "Michael Jackson", "Katy Perry",
    "Lady Gaga", "Post Malone", "Harry Styles", "Olivia Rodrigo", "SZA",
    "Sia", "Sam Smith", "Mariah Carey", "Celine Dion", "Britney Spears",
    "Christina Aguilera", "Usher", "Alicia Keys", "John Legend",
    "Charlie Puth", "Shawn Mendes", "Camila Cabello", "Selena Gomez",
    "Miley Cyrus", "Doja Cat", "Lizzo", "Chris Brown", "Frank Ocean",
    "Madonna", "George Michael", "BTS", "Blackpink",
    # rock
    "Coldplay", "Imagine Dragons", "Queen", "The Beatles", "Metallica",
    "Linkin Park", "Red Hot Chili Peppers", "Foo Fighters", "Radiohead",
    "U2", "Elton John", "David Bowie", "Prince", "Amy Winehouse",
    "Ozzy Osbourne", "Nirvana", "Guns N' Roses", "AC/DC", "Pink Floyd",
    "Led Zeppelin", "The Rolling Stones", "Fleetwood Mac", "Green Day",
    "Arctic Monkeys", "Twenty One Pilots", "Panic! At The Disco",
    "My Chemical Romance", "Muse", "The Killers", "OneRepublic",
    # hip-hop / rap
    "Eminem", "Kendrick Lamar", "Kanye West", "Jay-Z", "Nicki Minaj",
    "Travis Scott", "Cardi B", "Lil Wayne", "Snoop Dogg", "Dr. Dre",
    "Tyler, The Creator", "J. Cole", "Future", "Megan Thee Stallion",
    # latina
    "Bad Bunny", "Shakira", "Rosalía", "J Balvin", "Karol G", "Maluma",
    "Daddy Yankee", "Ozuna", "Enrique Iglesias", "Ricky Martin",
    "Luis Fonsi", "Anitta",
    # eletrónica
    "Daft Punk", "Calvin Harris", "David Guetta", "Avicii", "Marshmello",
    # clássicos
    "Elvis Presley", "Bob Marley", "Stevie Wonder", "Whitney Houston",
    "Bee Gees", "ABBA", "Maroon 5",
]


def eh_internacional(artista: str) -> bool:
    return normalizar(artista) in {normalizar(a) for a in ARTISTAS_INTERNACIONAIS}


def todos_os_artistas() -> list[str]:
    return ARTISTAS + ARTISTAS_INTERNACIONAIS


def artistas_do_dia(data: dt.date, quantos: int, lista: list[str] | None = None) -> list[str]:
    lista = lista if lista is not None else ARTISTAS
    aleatorio = random.Random(data.isoformat())
    return aleatorio.sample(lista, min(quantos, len(lista)))


def limpar_titulo(t: str) -> str:
    t = re.sub(
        r"\s*[\(\[][^\)\]]*(remaster|remix|ao vivo|live|version|edit|feat)[^\)\]]*[\)\]]",
        "", t or "", flags=re.I,
    )
    return t.strip()


def normalizar(t: str) -> str:
    t = unicodedata.normalize("NFD", t or "")
    t = "".join(c for c in t if unicodedata.category(c) != "Mn")
    return re.sub(r"[^A-Z0-9]", "", t.upper())


# ---------------------------------------------------------------- gerador de grelha

def gerar_grelha(entradas: list[dict]) -> dict:
    itens = sorted(
        (
            {"entradaId": e["id"], "palavra": normalizar(e["resposta"])}
            for e in entradas if len(normalizar(e["resposta"])) >= 2
        ),
        key=lambda i: -len(i["palavra"]),
    )
    if not itens:
        return {"erro": "sem respostas válidas"}

    mapa: dict[tuple[int, int], str] = {}
    colocadas: list[dict] = []
    falhadas: list[str] = []

    def testar(p, r, c, direcao):
        if any(b["r"] == r and b["c"] == c and b["dir"] == direcao for b in colocadas):
            return None  # já há uma palavra a começar exatamente aqui, na mesma direção
        dr, dc = (1, 0) if direcao == "down" else (0, 1)
        if mapa.get((r - dr, c - dc)):
            return None
        if mapa.get((r + dr * len(p), c + dc * len(p))):
            return None
        cruz = 0
        for i, letra in enumerate(p):
            rr, cc = r + dr * i, c + dc * i
            existente = mapa.get((rr, cc))
            if existente:
                if existente != letra:
                    return None
                cruz += 1
            else:
                pr, pc = (1, 0) if direcao == "across" else (0, 1)
                if mapa.get((rr - pr, cc - pc)) or mapa.get((rr + pr, cc + pc)):
                    return None
        return cruz

    def assentar(item, r, c, direcao):
        dr, dc = (1, 0) if direcao == "down" else (0, 1)
        for i, letra in enumerate(item["palavra"]):
            mapa[(r + dr * i, c + dc * i)] = letra
        colocadas.append({**item, "r": r, "c": c, "dir": direcao})

    assentar(itens[0], 0, 0, "across")

    def centro():
        if not colocadas:
            return 0.0, 0.0
        return (sum(p["r"] for p in colocadas) / len(colocadas),
                sum(p["c"] for p in colocadas) / len(colocadas))

    def melhor_encaixe(item):
        melhor = None
        cr, cc = centro()
        for base in list(colocadas):
            nova_dir = "down" if base["dir"] == "across" else "across"
            for bi, lb in enumerate(base["palavra"]):
                for wi, lw in enumerate(item["palavra"]):
                    if lb != lw:
                        continue
                    br = base["r"] + (bi if base["dir"] == "down" else 0)
                    bc = base["c"] + (bi if base["dir"] == "across" else 0)
                    r = br - (wi if nova_dir == "down" else 0)
                    c = bc - (wi if nova_dir == "across" else 0)
                    cruz = testar(item["palavra"], r, c, nova_dir)
                    if not cruz:
                        continue
                    nota = cruz * 100 - (abs(r - cr) + abs(c - cc))
                    if not melhor or nota > melhor["nota"]:
                        melhor = {"r": r, "c": c, "dir": nova_dir, "nota": nota}
        return melhor

    # Várias passagens: uma palavra que não encaixou na primeira ronda pode
    # encaixar depois de outras já estarem colocadas — não deitar fora à primeira.
    pendentes = itens[1:]
    progresso = True
    while progresso and pendentes:
        progresso = False
        restantes = []
        for item in pendentes:
            melhor = melhor_encaixe(item)
            if melhor:
                assentar(item, melhor["r"], melhor["c"], melhor["dir"])
                progresso = True
            else:
                restantes.append(item)
        pendentes = restantes
    falhadas = [p["palavra"] for p in pendentes]

    if not colocadas:
        return {"erro": "nada encaixou"}

    def extremo_r(p):
        return p["r"] + (len(p["palavra"]) - 1 if p["dir"] == "down" else 0)
    def extremo_c(p):
        return p["c"] + (len(p["palavra"]) - 1 if p["dir"] == "across" else 0)

    min_r = min(p["r"] for p in colocadas)
    min_c = min(p["c"] for p in colocadas)
    max_r = max(extremo_r(p) for p in colocadas)
    max_c = max(extremo_c(p) for p in colocadas)
    for p in colocadas:
        p["r"] -= min_r
        p["c"] -= min_c
    colocadas.sort(key=lambda p: (p["r"], p["c"]))

    numeros: dict[tuple[int, int], int] = {}
    proximo = 1
    for p in colocadas:
        chave = (p["r"], p["c"])
        if chave not in numeros:
            numeros[chave] = proximo
            proximo += 1
        p["num"] = numeros[chave]

    return {
        "linhas": max_r - min_r + 1,
        "colunas": max_c - min_c + 1,
        "colocadas": colocadas,
        "falhadas": falhadas,
    }


# ---------------------------------------------------------------- base de dados

class Base(DeclarativeBase):
    pass


class Faixa(Base):
    """O catálogo. Cresce com o tempo — nunca se apaga uma linha daqui,
    só se marca quando foi usada, para não repetir cedo demais."""
    __tablename__ = "faixas"
    id: Mapped[str] = mapped_column(String, primary_key=True)   # id da faixa na Deezer
    titulo: Mapped[str] = mapped_column(String)
    artista: Mapped[str] = mapped_column(String)
    album: Mapped[str] = mapped_column(String, default="")
    capa: Mapped[str] = mapped_column(String, default="")
    audio_origem: Mapped[str] = mapped_column(String)
    genero: Mapped[str] = mapped_column(String, default="")
    decada: Mapped[int | None] = mapped_column(Integer, nullable=True)
    adicionada_em: Mapped[str] = mapped_column(String)
    ultima_utilizacao: Mapped[str | None] = mapped_column(String, nullable=True)


class PuzzleGuardado(Base):
    __tablename__ = "puzzles"
    data: Mapped[str] = mapped_column(String, primary_key=True)  # AAAA-MM-DD
    conteudo: Mapped[dict] = mapped_column(JSON)


class Jogador(Base):
    """Estatísticas públicas e leves para comparação entre amigos — sem
    contas, sem password. Cada pessoa tem um código curto gerado no
    próprio dispositivo (guardado em localStorage) que pode partilhar;
    quem tiver o código consegue ver as estatísticas, tal como um
    perfil público de jogo. Não guarda nada sensível."""
    __tablename__ = "jogadores"
    codigo: Mapped[str] = mapped_column(String, primary_key=True)
    nome: Mapped[str] = mapped_column(String, default="Jogador")
    total: Mapped[int] = mapped_column(Integer, default=0)
    sem_ajuda: Mapped[int] = mapped_column(Integer, default=0)
    streak: Mapped[int] = mapped_column(Integer, default=0)
    atualizado_em: Mapped[str] = mapped_column(String, default="")


class Conta(Base):
    """Conta real (email + password), para a identidade e o código
    sobreviverem a limpar o browser ou mudar de dispositivo — ao
    contrário do código simples do Jogador, que só vive no localStorage
    de um aparelho. Uma conta está sempre ligada a um código de Jogador,
    reaproveitando as estatísticas e a lista de amigos já existentes."""
    __tablename__ = "contas"
    email: Mapped[str] = mapped_column(String, primary_key=True)
    senha_hash: Mapped[str] = mapped_column(String)
    nome: Mapped[str] = mapped_column(String, default="Jogador")
    codigo: Mapped[str] = mapped_column(String)
    criada_em: Mapped[str] = mapped_column(String, default="")


class SessaoConta(Base):
    """Um token de sessão simples (não é JWT) — basta gerar um valor
    aleatório imprevisível e guardá-lo; o cliente manda-o de volta no
    cabeçalho Authorization. Apagar a linha equivale a terminar sessão."""
    __tablename__ = "sessoes_conta"
    token: Mapped[str] = mapped_column(String, primary_key=True)
    email: Mapped[str] = mapped_column(String)
    criada_em: Mapped[str] = mapped_column(String, default="")


class ProgressoConta(Base):
    """O progresso de um puzzle específico (respostas na grelha, se levou
    ajuda, etc.), ligado a uma conta — para abrires noutro dispositivo e
    continuares exatamente onde ficaste. Uma linha por (conta, puzzle)."""
    __tablename__ = "progresso_conta"
    email: Mapped[str] = mapped_column(String, primary_key=True)
    puzzle_id: Mapped[str] = mapped_column(String, primary_key=True)
    conteudo: Mapped[dict] = mapped_column(JSON)
    concluido: Mapped[bool] = mapped_column(default=False)
    sem_ajuda: Mapped[bool | None] = mapped_column(nullable=True)
    atualizado_em: Mapped[str] = mapped_column(String, default="")


engine = create_async_engine(BASE_DE_DADOS, connect_args=_connect_args)
Sessao = async_sessionmaker(engine, expire_on_commit=False)


# ---------------------------------------------------------------- Deezer

cliente: httpx.AsyncClient | None = None


# Alguns nomes são ambíguos na pesquisa da Deezer (há homónimos noutros
# países) — para estes, usa-se sempre o id exato em vez de confiar na busca.
IDS_ARTISTA_DEEZER: dict[str, int] = {
    "Agir": 665993,  # o português (Bernardo Costa) — não o rapper alemão do mesmo nome
}


MUSICAS_CONHECIDAS: dict[str, list[str]] = {
    # Confirmadas por pesquisa fora da Deezer (Wikipédia, imprensa, etc.) —
    # não é o "top" da própria Deezer, que já vimos poder estar
    # contaminado por artistas homónimos. Lista pequena de propósito;
    # cresce aos poucos, artista a artista, à medida que se confirma.
    "Taylor Swift": [
        "Blank Space", "Shake It Off", "Love Story", "Anti-Hero",
    ],
    "Amália Rodrigues": [
        "Uma Casa Portuguesa", "Estranha Forma de Vida",
        "Povo Que Lavas no Rio", "Gaivota", "Coimbra",
    ],
    "Mariza": [
        "Chuva", "Ó Gente da Minha Terra", "Barco Negro",
        "Meu Fado Meu", "Maria Lisboa",
    ],
    "Zeca Afonso": [
        "Grândola, Vila Morena",
    ],
    "Carminho": [
        "Perdóname", "As Pedras da Minha Rua",
    ],
    "Ana Moura": [
        "Dia de Folga", "Desfado", "Andorinhas",
    ],
    "Gisela João": [
        "Sr. Extraterrestre",
    ],
    "Cuca Roseta": [
        "Rua do Capelão",
    ],
    "Raquel Tavares": [
        "Meu Amor de Longe",
    ],
    "Sara Correia": [
        "Chegou Tão Tarde", "Quero é Viver",
    ],
    "Sérgio Godinho": [
        "O Primeiro Dia", "É Terça-Feira", "Com um Brilhozinho nos Olhos",
    ],
    "Rui Veloso": [
        "Porto Sentido", "Chico Fininho",
    ],
    "Xutos & Pontapés": [
        "A Minha Casinha",
    ],
    "GNR": [
        "Dunas", "Pronúncia do Norte",
    ],
    "Ornatos Violeta": [
        "Ouvi Dizer", "A Dama do Sinal",
    ],
    "Pedro Abrunhosa": [
        "Momento", "Tudo o Que Eu Te Dou", "Não Desistas de Mim",
    ],
    "Capitão Fausto": [
        "Amanhã Tou Melhor", "Morro na Praia",
    ],
    "Toranja": [
        "Carta", "Fogo e Noite",
    ],
    "Delfins": [
        "A Baía de Cascais", "Sou Como Um Rio",
    ],
    "D'ZRT": [
        "Para Mim Tanto Me Faz", "Quero Voltar",
    ],
    "Anjos": [
        "Ficarei", "É o Amor",
    ],
    "Da Weasel": [
        "Re-Tratamento", "Força (Uma Página de História)", "Todagente",
    ],
    "Slow J": [
        "Só Queria Sorrir", "FAM", "Também Sonhar",
    ],
    "Plutónio": [
        "Meu Deus", "Cafeína",
    ],
    "Papillon": [
        "Sweet Spot", "Iminente",
    ],
    "Dino D'Santiago": [
        "Nu Bai",
    ],
    "Mishlawi": [
        "All Night", "Always On My Mind",
    ],
    "Bispo": [
        "Essa Saia", "NÓS2",
    ],
    "Boss AC": [
        "Sexta-Feira (Emprego Bom Já)", "Baza, Baza",
    ],
    "Regula": [
        "Casanova",
    ],
    "Piruka": [
        "Ca Bu Fla Ma Nau", "Se Eu Não Acordar Amanhã", "Salto Alto",
    ],
    "Expensive Soul": [
        "O Amor É Mágico", "13 Mulheres",
    ],
    "Toy": [
        "Sou Português",
    ],
    "Mizzy Miles": [
        "Europa", "Bênção",
    ],
    "Nga": [
        "Deus Me Perdoa",
    ],
    "Karetus": [
        "Future Is Now",
    ],
    "The Gift": [
        "Driving You Slow", "Primavera",
    ],
    "Sara Tavares": [
        "Chamar a Música", "Eu Sei",
    ],
    "Julinho KSD": [
        "Sentimento Safari", "Vivi Good",
    ],
    "Nenny": [
        "Sushi", "Bússola",
    ],
    "Sam The Kid": [
        "16/12/95", "Poetas de Karaoke",
    ],
    "Valete": [
        "Roleta Russa", "Anti-Herói",
    ],
    "Mundo Segundo": [
        "Bate Palmas",
    ],
    "ProfJam": [
        "Água de Coco", "Malibu",
    ],
    "HMB": [
        "O Amor É Assim",
    ],
    "Wet Bed Gang": [
        "Devia Ir", "Bairro",
    ],
    "Buraka Som Sistema": [
        "Sound of Kuduro", "Kalemba (Wegue Wegue)",
    ],
    "Calema": [
        "A Nossa Vez",
    ],
    "Anselmo Ralph": [
        "Não Me Toca",
    ],
    "C4 Pedro": [
        "Vamos Ficar Por Aqui",
    ],
    "Ivandro": [
        "Lua", "Como Tu", "Essa Saia",
    ],
    "Agir": [
        "Parte-me o Pescoço", "Wella",
    ],
    "T-Rex": [
        "Dr. Bayard", "Gang Gang",
    ],
    "D.A.M.A": [
        "Balada do Desajeitado", "Luísa",
    ],
    "Buba Espinho": [
        "Roubei-te um Beijo",
    ],
    "Chico da Tina": [
        "Ronaldo", "Resort",
    ],
    "GROGNation": [
        "Distante", "Dá-me Espaço",
    ],
    "Nininho Vaz Maia": [
        "E Agora",
    ],
    "Gama WNTD": [
        "Borboletas",
    ],
    "ATOA": [
        "Tu na Tua", "Distância",
    ],
    "LON3R JOHNY": [
        "DEATH NOTE",
    ],
    "9 Miller": [
        "Filho da Guida", "Limonada",
    ],
    "Hollyhood": [
        "Fácil", "Cobras e Ratazanas", "Miúda",
    ],
    "Dillaz": [
        "Alô", "Juvena",
    ],
    "Richie Campbell": [
        "Do You No Wrong", "That's How We Roll",
    ],
    "Salvador Sobral": [
        "Amar Pelos Dois",
    ],
    "Bárbara Tinoco": [
        "Antes Dela Dizer Que Sim", "Chamada Não Atendida",
    ],
    "Diogo Piçarra": [
        "Tu e Eu", "Monarquia", "Trevo",
    ],
    "Aurea": [
        "Busy for Me", "Okay Alright",
    ],
    "Ana Bacalhau": [
        "O Erro Mais Bonito",
    ],
    "Miguel Araújo": [
        "Os Maridos das Outras", "Dona Laura",
    ],
    "David Carreira": [
        "Esta Noite", "Ficamos Por Aqui",
    ],
    "Fernando Daniel": [
        "Voltas", "Se Eu",
    ],
    "Cláudia Pascoal": [
        "O Jardim",
    ],
    "Iolanda": [
        "Grito",
    ],
    "Bárbara Bandeira": [
        "Como Tu",
    ],
    "Blaya": [
        "Faz Gostoso",
    ],
    "Mafalda Veiga": [
        "Planície",
    ],
    "Rita Guerra": [
        "Deixa-me Sonhar (Só Mais Uma Vez)",
    ],
    "Van Zee": [
        "Tempo", "Alma Nua",
    ],
    "Carolina Deslandes": [
        "A Vida Toda", "Avião de Papel",
    ],
    "MARO": [
        "Saudade, Saudade",
    ],
    "NAPA": [
        "Deslocado",
    ],
    "Vizinhos": [
        "Pôr do Sol", "Pobre Ex-Namorado",
    ],
    "Soraia Ramos": [
        "Bai", "BKBN", "O Nosso Amor",
    ],
    "Pedro Mafama": [
        "Preço Certo",
    ],
    "Quim Barreiros": [
        "A Garagem da Vizinha", "Bacalhau à Portuguesa", "O Sorveteiro",
    ],
    "Tony Carreira": [
        "Ai Destino", "Depois de Ti Mais Nada",
    ],
    "Emanuel": [
        "Pimba Pimba",
    ],
    "Ana Malhoa": [
        "Sube la Temperatura", "Tá Turbinada",
    ],
    "Marco Paulo": [
        "Eu Tenho Dois Amores", "Ninguém, Ninguém",
    ],
    "Dama": [
        "CASA", "Loucamente", "Era Eu", "Mãe", "Por ti Amor", "Ficar Óai",
    ],
    "Isak": [
        "Calipo De Cerveja", "Max Win", "Mia Fernandes", "Batota",
        "Bada Bing", "Drip Fashion", "Sergio Tacchini", "Eu Vou Ao Bairro",
        "Seguir Em Frente", "Bar Da Praia", "Telescópio", "Grab And Go",
        "Picheleiro", "Unhas Pintadas",
    ],
    "Zigarro": [
        "Calipo De Cerveja", "Max Win", "Mia Fernandes", "Batota",
        "Bada Bing", "Drip Fashion", "Sergio Tacchini", "Eu Vou Ao Bairro",
        "Seguir Em Frente", "Bar Da Praia", "Telescópio", "Grab And Go",
        "Picheleiro", "Unhas Pintadas",
    ],
    "Armando Teles": [
        "Calipo De Cerveja", "Max Win", "Mia Fernandes", "Batota",
        "Bada Bing", "Drip Fashion", "Sergio Tacchini", "Eu Vou Ao Bairro",
        "Seguir Em Frente", "Bar Da Praia", "Telescópio", "Grab And Go",
        "Picheleiro", "Unhas Pintadas",
    ],
}


async def explorar_artista(artista: str) -> list[dict]:
    """Até 6 faixas com excerto disponível para um artista."""
    id_conhecido = IDS_ARTISTA_DEEZER.get(artista)
    if id_conhecido:
        artista_id = id_conhecido
    else:
        try:
            r = await cliente.get(f"{DEEZER}/search/artist", params={"q": artista, "limit": 5})
            achados = (r.json() or {}).get("data") or []
        except Exception as erro:
            print(f"[tugle]   {artista}: falhou a pesquisa de artista ({erro})")
            return []
        if not achados:
            print(f"[tugle]   {artista}: a Deezer não encontrou este artista")
            return []
        # A Deezer às vezes devolve um homónimo em vez do artista certo
        # (ex.: pesquisar "Ana" pode encontrar um artista qualquer chamado
        # Ana, nada a ver com o que queremos) — só aceitamos se o nome
        # devolvido bater certo com o que pedimos, letra por letra depois
        # de normalizado. Sem correspondência exata, mais vale não ter
        # faixas nenhumas do que ter faixas do artista errado.
        alvo = normalizar(artista)
        correspondencia = next(
            (a for a in achados if normalizar(a.get("name", "")) == alvo), None
        )
        if not correspondencia:
            nomes = ", ".join(a.get("name", "?") for a in achados[:3])
            print(f"[tugle]   {artista}: a Deezer só encontrou homónimos diferentes ({nomes}) — a ignorar")
            return []
        artista_id = correspondencia["id"]

    def para_entrada(faixa: dict) -> dict:
        return {
            "id": str(faixa["id"]),
            "titulo": limpar_titulo(faixa.get("title_short") or faixa.get("title", "")),
            "artista": faixa.get("artist", {}).get("name", artista),
            "album": faixa.get("album", {}).get("title", ""),
            "album_id": faixa.get("album", {}).get("id"),
            "capa": faixa.get("album", {}).get("cover_medium", ""),
            "audio": faixa["preview"],
        }

    faixas: list[dict] = []
    ids_vistos: set[int] = set()

    # Prioridade 1: músicas confirmadas como famosas por pesquisa externa
    # — vamos buscar especificamente essas à Deezer (só para o áudio),
    # em vez de confiar na ordenação interna dela.
    for titulo in MUSICAS_CONHECIDAS.get(artista, []):
        try:
            r = await cliente.get(f"{DEEZER}/search/track", params={
                "q": f'artist:"{artista}" track:"{titulo}"', "limit": 1,
            })
            achadas = (r.json() or {}).get("data") or []
        except Exception:
            continue
        if not achadas or not achadas[0].get("preview"):
            continue
        if achadas[0]["id"] in ids_vistos:
            continue
        ids_vistos.add(achadas[0]["id"])
        faixas.append(para_entrada(achadas[0]))
        if len(faixas) >= 6:
            return faixas

    # Prioridade 2: completar (ou, se não houver lista curada, usar
    # exclusivamente) com o "top tracks" da Deezer.
    try:
        r = await cliente.get(f"{DEEZER}/artist/{artista_id}/top", params={"limit": 20})
        topo = (r.json() or {}).get("data") or []
    except Exception as erro:
        print(f"[tugle]   {artista}: falhou a lista de faixas ({erro})")
        return faixas

    for faixa in topo:
        if not faixa.get("preview") or faixa["id"] in ids_vistos:
            continue
        ids_vistos.add(faixa["id"])
        faixas.append(para_entrada(faixa))
        if len(faixas) >= 6:
            break
    if not faixas:
        print(f"[tugle]   {artista}: encontrado, mas nenhuma faixa tem excerto (preview vazio)")
    return faixas


TRADUCAO_GENEROS = {
    "afrikanische musik": "Música africana",
    "brasilianische musik": "Música brasileira",
    "musique africaine": "Música africana",
    "musique brésilienne": "Música brasileira",
    "african music": "Música africana",
    "brazilian music": "Música brasileira",
    "singer & songwriter": "Singer-songwriter",
}


def genero_traduzido(genero: str | None) -> str | None:
    if not genero:
        return genero
    return TRADUCAO_GENEROS.get(genero.strip().lower(), genero)


async def genero_e_decada(album_id) -> tuple[str, int | None]:
    if not album_id:
        return "", None
    try:
        r = await cliente.get(f"{DEEZER}/album/{album_id}")
        d = r.json() or {}
        genero = ((d.get("genres") or {}).get("data") or [{}])[0].get("name", "")
        lancamento = d.get("release_date", "") or ""
        decada = int(lancamento[:3] + "0") if len(lancamento) >= 4 and lancamento[:4].isdigit() else None
        return genero_traduzido(genero) or "", decada
    except Exception:
        return "", None


async def garantir_catalogo(minimo: int, limite_por_chamada: int = 25) -> None:
    """Faz o catálogo crescer até ao mínimo, mas nunca explora mais que
    `limite_por_chamada` artistas de uma vez — sem este limite, quando o
    catálogo precisa de crescer muito (ex.: logo a seguir à meia-noite),
    esta função pode demorar minutos e o pedido que a disparou (o
    /puzzle/hoje de alguém) acaba por desistir a meio, dando um erro
    mesmo que o trabalho continue a acontecer por trás. Com o limite,
    cada chamada é rápida — o catálogo cresce um pouco de cada vez que
    é preciso, em vez de tudo de uma só vez."""
    async with Sessao() as sessao:
        total = len((await sessao.execute(select(Faixa.id))).all())
        if total >= minimo:
            return

        print(f"[tugle] catálogo tem {total} faixas, a construir até {minimo} (até {limite_por_chamada} artistas nesta chamada)…")
        explorados = 0
        for artista in artistas_do_dia(dt.date.today(), len(todos_os_artistas()), todos_os_artistas()):
            if total >= minimo or explorados >= limite_por_chamada:
                break
            explorados += 1
            novas = await explorar_artista(artista)
            adicionadas = 0
            for f in novas:
                if await sessao.get(Faixa, f["id"]):
                    continue
                genero, decada = await genero_e_decada(f.get("album_id"))
                sessao.add(Faixa(
                    id=f["id"], titulo=f["titulo"], artista=f["artista"],
                    album=f.get("album", ""), capa=f["capa"], audio_origem=f["audio"],
                    genero=genero, decada=decada,
                    adicionada_em=dt.date.today().isoformat(), ultima_utilizacao=None,
                ))
                total += 1
                adicionadas += 1
            if adicionadas:
                print(f"[tugle]   {artista}: +{adicionadas} faixas (total {total})")
            await sessao.commit()
        print(f"[tugle] catálogo final: {total} faixas")


# ---------------------------------------------------------------- montagem do puzzle diário

STOPWORDS_RESPOSTA = {
    "A", "AS", "O", "OS", "UM", "UMA", "UNS", "UMAS",
    "DE", "DA", "DO", "DAS", "DOS", "EM", "NA", "NO", "NAS", "NOS",
    "E", "OU", "MAS", "SE", "QUE", "COM", "SEM", "POR", "PARA", "PRA",
    "NAO", "SIM", "JA", "SO", "AI", "LA", "CA", "AQUI", "ALI",
    "EU", "TU", "ELE", "ELA", "NOS", "VOS", "ELES", "ELAS", "TE", "ME", "SE",
    "MEU", "TEU", "SEU", "MINHA", "TUA", "SUA", "TEUS", "SEUS",
    "ESTE", "ESTA", "ESSE", "ESSA", "ISTO", "ISSO", "AQUELE", "AQUELA",
    "VOU", "VAI", "VAO", "ESTA", "ESTAO", "É", "ERA", "FOI", "SER", "ESTAR",
    "MAIS", "MENOS", "MUITO", "POUCO", "AO", "AOS", "PELO", "PELA",
    "ATE", "DESDE", "ENTAO", "ASSIM", "COMO", "QUANDO", "ONDE", "PORQUE",
}


def eh_stopword(palavra: str) -> bool:
    return normalizar(palavra) in STOPWORDS_RESPOSTA


def candidatos_resposta(faixa: "Faixa") -> list[tuple[str, str]]:
    """Todas as hipóteses válidas de resposta para esta música, cada uma
    com várias frases possíveis — a curta e direta é só mais uma opção,
    não a única, para não ficar sempre a mesma fórmula repetida."""
    titulo = (faixa.titulo or "").strip()
    artista = (faixa.artista or "").strip()
    decada = faixa.decada
    genero = genero_traduzido(faixa.genero) or None
    candidatos: list[tuple[str, str]] = []

    def cabe(palavra: str) -> bool:
        return 3 <= len(normalizar(palavra)) <= 14

    if cabe(titulo):
        frases = ["Título da música.", f"Uma música de {artista}."]
        if decada:
            frases.append(f"Música de {artista}, dos anos {decada}.")
        if genero:
            frases.append(f"Um tema de {genero}, de {artista}.")
        candidatos.extend((titulo, f) for f in frases)

    if cabe(artista):
        frases = ["Nome do artista.", f"Quem canta “{titulo}”?"]
        if decada:
            frases.append(f"“{titulo}”, dos anos {decada}. Quem canta?")
        if genero:
            frases.append(f"Um tema de {genero} chamado “{titulo}”. Quem o canta?")
        candidatos.extend((artista, f) for f in frases)

    palavras_titulo = titulo.split()
    if len(palavras_titulo) > 1:
        if cabe(palavras_titulo[0]) and not eh_stopword(palavras_titulo[0]):
            resto = " ".join(palavras_titulo[1:])
            candidatos.append((palavras_titulo[0], "Primeira palavra do título."))
            candidatos.append((palavras_titulo[0], f"Como começa “___ {resto}”?"))
        if (palavras_titulo[-1] != palavras_titulo[0] and cabe(palavras_titulo[-1])
                and not eh_stopword(palavras_titulo[-1])):
            resto = " ".join(palavras_titulo[:-1])
            candidatos.append((palavras_titulo[-1], "Última palavra do título."))
            candidatos.append((palavras_titulo[-1], f"Como termina “{resto} ___”?"))

    palavras_artista = artista.split()
    if len(palavras_artista) > 1:
        if cabe(palavras_artista[0]) and not eh_stopword(palavras_artista[0]):
            resto = " ".join(palavras_artista[1:])
            candidatos.append((palavras_artista[0], "Primeira palavra do nome do artista."))
            candidatos.append((palavras_artista[0], f"Como começa o nome “___ {resto}”?"))

    return candidatos


def escolher_entrada(faixa: "Faixa", semente: str, usados: set[str]) -> tuple[str, str] | None:
    """(resposta, pista) escolhidos de forma estável entre as hipóteses
    válidas — ou None se nenhuma hipótese couber na grelha (3 a 14
    letras), ou se todas as hipóteses desta música já tiverem sido usadas
    por outra entrada deste mesmo puzzle (ex.: duas músicas do mesmo
    artista, ambas a tentar usar o nome do artista como resposta)."""
    candidatos = candidatos_resposta(faixa)
    if not candidatos:
        return None
    ordem = candidatos[:]
    random.Random(semente + faixa.id).shuffle(ordem)
    for resposta, pista in ordem:
        chave = normalizar(resposta)
        if chave not in usados:
            usados.add(chave)
            return (resposta, pista)
    return None  # todas as hipóteses desta música já estavam ocupadas

    aleatorio = random.Random(semente + faixa.id)
    return aleatorio.choice(modelos)


async def montar_puzzle(data: dt.date) -> dict:
    await garantir_catalogo(TAMANHO_MINIMO_CATALOGO)

    limite = (data - dt.timedelta(days=DIAS_ATE_REPETIR)).isoformat()
    async with Sessao() as sessao:
        resultado = await sessao.execute(
            select(Faixa).where(
                (Faixa.ultima_utilizacao.is_(None)) | (Faixa.ultima_utilizacao < limite)
            )
        )
        candidatas = list(resultado.scalars().all())

    # descarta só se NENHUMA hipótese de resposta servir (título, artista,
    # ou uma palavra isolada de qualquer um dos dois — ver candidatos_resposta)
    candidatas = [f for f in candidatas if candidatos_resposta(f)]

    # ignora sempre quem já não está na lista ARTISTAS — evita que alguém
    # removido continue a aparecer só porque ficou guardado no catálogo
    artistas_atuais = {normalizar(a) for a in ARTISTAS}
    candidatas = [f for f in candidatas if normalizar(f.artista) in artistas_atuais]

    tema_hoje = tema_do_dia(data)
    nome_tema = None
    if tema_hoje:
        nome_tema, artistas_tema = tema_hoje
        tematicas = [f for f in candidatas if f.artista in artistas_tema]
        if len(tematicas) >= 6:
            candidatas = tematicas
        else:
            nome_tema = None  # não havia o suficiente — segue o catálogo normal, sem tema

    if len(candidatas) < 6:
        raise RuntimeError(
            f"O catálogo só tem {len(candidatas)} faixas por usar (título entre 3 e 14 "
            "letras — precisa de pelo menos 6. Olha para o terminal do servidor: as linhas "
            "'[tugle] ...' dizem porque é que a exploração de artistas na Deezer não "
            "trouxe faixas suficientes."
        )

    aleatorio = random.Random(data.isoformat())
    aleatorio.shuffle(candidatas)
    candidatas = candidatas[:ENTRADAS_POR_PUZZLE]

    entradas = []
    respostas_usadas: set[str] = set()
    for f in candidatas:
        escolha = escolher_entrada(f, data.isoformat(), respostas_usadas)
        if not escolha:
            continue
        resposta, pista = escolha
        entradas.append({
            "id": f.id, "resposta": resposta, "titulo": f.titulo, "artista": f.artista,
            "capa": f.capa, "genero": genero_traduzido(f.genero), "decada": f.decada,
            "pista": pista, "inicio": INICIO_EXCERTO_SEGUNDOS,
        })

    grelha = gerar_grelha(entradas)
    if grelha.get("erro") or len(grelha.get("colocadas", [])) < 5:
        raise RuntimeError(f"Não consegui montar puzzle de {data} com o catálogo atual.")

    ids_colocados = {c["entradaId"] for c in grelha["colocadas"]}
    entradas_finais = [e for e in entradas if e["id"] in ids_colocados]

    return {
        "id": data.isoformat(),
        "nome": f"Tugle de {data.strftime('%d/%m/%Y')}" + (f" — {nome_tema}" if nome_tema else ""),
        "data": data.isoformat(),
        "tema": nome_tema,
        "entradas": entradas_finais,
        "grelha": {
            "linhas": grelha["linhas"], "colunas": grelha["colunas"],
            "colocadas": grelha["colocadas"],
        },
    }


def id_puzzle_modo(data: dt.date, origem: str, decada: int | None) -> str:
    sufixo_origem = origem if origem in ("nacional", "internacional") else "todos"
    sufixo_decada = str(decada) if decada else "todas"
    return f"{data.isoformat()}--{sufixo_origem}--{sufixo_decada}"


async def montar_lista_stream(origem: str, decada: int | None, quantidade: int) -> list[dict]:
    """Para a página de stream — ao contrário do puzzle normal, é gerado
    na hora, sempre diferente, sem grelha (não faz falta, o stream mostra
    uma música de cada vez) e sem ficar gravado. É assim de propósito:
    o streamer quer poder jogar várias rondas diferentes ao longo do dia,
    não o mesmo puzzle fixo."""
    async with Sessao() as sessao:
        candidatas = list((await sessao.execute(select(Faixa))).scalars().all())

    candidatas = [f for f in candidatas if candidatos_resposta(f)]
    if origem == "nacional":
        candidatas = [f for f in candidatas if not eh_internacional(f.artista)]
    elif origem == "internacional":
        candidatas = [f for f in candidatas if eh_internacional(f.artista)]
    if decada:
        candidatas = [f for f in candidatas if f.decada == decada]

    if len(candidatas) < min(quantidade, 6):
        raise RuntimeError(
            f"Só há {len(candidatas)} faixas com este filtro — tenta pedir menos músicas, "
            "ou muda a origem/década."
        )

    semente = f"stream-{uuid4()}"
    aleatorio = random.Random(semente)
    aleatorio.shuffle(candidatas)
    candidatas = candidatas[:quantidade]

    entradas = []
    respostas_usadas: set[str] = set()
    for f in candidatas:
        escolha = escolher_entrada(f, semente, respostas_usadas)
        if not escolha:
            continue
        resposta, pista = escolha
        entradas.append({
            "id": f.id, "resposta": resposta, "titulo": f.titulo, "artista": f.artista,
            "capa": f.capa, "genero": genero_traduzido(f.genero), "decada": f.decada,
            "pista": pista, "inicio": INICIO_EXCERTO_SEGUNDOS,
        })
    return entradas


async def montar_puzzle_modo(data: dt.date, origem: str, decada: int | None) -> dict:
    """Puzzle diário de um modo (origem e/ou década) — tal como o puzzle
    de hoje normal, é gravado e partilhado: todos os que escolherem a
    mesma combinação no mesmo dia veem exatamente o mesmo puzzle. Nunca
    gerado na hora."""
    async with Sessao() as sessao:
        candidatas = list((await sessao.execute(select(Faixa))).scalars().all())

    candidatas = [f for f in candidatas if candidatos_resposta(f)]
    if origem == "nacional":
        candidatas = [f for f in candidatas if not eh_internacional(f.artista)]
    elif origem == "internacional":
        candidatas = [f for f in candidatas if eh_internacional(f.artista)]
    if decada:
        candidatas = [f for f in candidatas if f.decada == decada]

    if len(candidatas) < 6:
        descricao = (f"dos anos {decada}" if decada else "") + (f" ({origem})" if origem != "todos" else "")
        raise RuntimeError(
            f"Só há {len(candidatas)} faixas {descricao or 'com este filtro'} — precisa de pelo menos 6. "
            "O catálogo ainda está a crescer nessa zona."
        )

    semente = id_puzzle_modo(data, origem, decada)
    aleatorio = random.Random(semente)
    aleatorio.shuffle(candidatas)
    candidatas = candidatas[:ENTRADAS_POR_PUZZLE]

    entradas = []
    respostas_usadas: set[str] = set()
    for f in candidatas:
        escolha = escolher_entrada(f, semente, respostas_usadas)
        if not escolha:
            continue
        resposta, pista = escolha
        entradas.append({
            "id": f.id, "resposta": resposta, "titulo": f.titulo, "artista": f.artista,
            "capa": f.capa, "genero": genero_traduzido(f.genero), "decada": f.decada,
            "pista": pista, "inicio": INICIO_EXCERTO_SEGUNDOS,
        })

    grelha = gerar_grelha(entradas)
    if grelha.get("erro") or len(grelha.get("colocadas", [])) < 5:
        raise RuntimeError(f"Não consegui montar este puzzle para {data}.")

    ids_colocados = {c["entradaId"] for c in grelha["colocadas"]}
    entradas_finais = [e for e in entradas if e["id"] in ids_colocados]

    nome_origem = {"nacional": "Nacional", "internacional": "Internacional"}.get(origem, "")
    partes_nome = [p for p in [nome_origem, f"anos {decada}" if decada else ""] if p]
    nome = f"Tugle de {data.strftime('%d/%m/%Y')}" + (" — " + ", ".join(partes_nome) if partes_nome else "")

    return {
        "id": id_puzzle_modo(data, origem, decada),
        "nome": nome,
        "data": data.isoformat(),
        "entradas": entradas_finais,
        "grelha": {
            "linhas": grelha["linhas"], "colunas": grelha["colunas"],
            "colocadas": grelha["colocadas"],
        },
    }


async def obter_ou_criar_modo(data: dt.date, origem: str, decada: int | None) -> dict:
    if origem == "todos" and not decada:
        return await obter_ou_criar(data)  # é literalmente o puzzle do dia normal
    pid = id_puzzle_modo(data, origem, decada)
    async with Sessao() as sessao:
        guardado = await sessao.get(PuzzleGuardado, pid)
        if guardado and not puzzle_desatualizado(guardado.conteudo):
            return guardado.conteudo
    puzzle = await montar_puzzle_modo(data, origem, decada)
    async with Sessao() as sessao:
        await sessao.merge(PuzzleGuardado(data=pid, conteudo=puzzle))
        await sessao.commit()
    return puzzle



async def gerar_e_guardar(data: dt.date) -> dict:
    puzzle = await montar_puzzle(data)
    async with Sessao() as sessao:
        await sessao.merge(PuzzleGuardado(data=data.isoformat(), conteudo=puzzle))
        for e in puzzle["entradas"]:
            faixa = await sessao.get(Faixa, e["id"])
            if faixa:
                faixa.ultima_utilizacao = data.isoformat()
        await sessao.commit()
    return puzzle


def para_cliente(puzzle: dict) -> dict:
    p = {**puzzle, "entradas": []}
    for e in puzzle["entradas"]:
        p["entradas"].append({**e, "audio": f"/audio/{e['id']}"})
    return p


def puzzle_desatualizado(puzzle: dict) -> bool:
    """Deteta puzzles gravados por uma versão antiga do gerador (sem pista,
    com respostas fora dos limites actuais, ou com a grelha a usar a chave
    antiga 'entrada_id' em vez de 'entradaId')."""
    ids_validos = {e.get("id") for e in puzzle.get("entradas", [])}
    grelha = puzzle.get("grelha", {})
    linhas, colunas = grelha.get("linhas", 0), grelha.get("colunas", 0)
    posicoes_vistas = set()
    for c in grelha.get("colocadas", []):
        if c.get("entradaId") not in ids_validos:
            return True
        comprimento = len(c.get("palavra", ""))
        if c.get("dir") == "down" and c.get("r", 0) + comprimento > linhas:
            return True
        if c.get("dir") == "across" and c.get("c", 0) + comprimento > colunas:
            return True
        chave_posicao = (c.get("r"), c.get("c"), c.get("dir"))
        if chave_posicao in posicoes_vistas:
            return True  # duas palavras diferentes a começar na mesma casa e direção
        posicoes_vistas.add(chave_posicao)
    artistas_atuais = {normalizar(a) for a in ARTISTAS}
    for e in puzzle.get("entradas", []):
        if not e.get("pista"):
            return True
        if not e.get("inicio"):
            return True
        if normalizar(e.get("artista", "")) not in artistas_atuais:
            return True
        if not (3 <= len(normalizar(e.get("resposta", ""))) <= 14):
            return True
        genero_bruto = (e.get("genero") or "").strip().lower()
        if genero_bruto in TRADUCAO_GENEROS:
            return True  # género ainda por traduzir (ex.: "Afrikanische Musik")
    return False


async def obter_ou_criar(data: dt.date) -> dict:
    async with Sessao() as sessao:
        guardado = await sessao.get(PuzzleGuardado, data.isoformat())
        if guardado and not puzzle_desatualizado(guardado.conteudo):
            return guardado.conteudo
    return await gerar_e_guardar(data)


# ---------------------------------------------------------------- ciclo de vida + agendador

agendador = AsyncIOScheduler(timezone=LISBOA)


async def tarefa_meia_noite() -> None:
    hoje = dt.datetime.now(LISBOA).date()
    try:
        await gerar_e_guardar(hoje)
    except Exception as erro:
        print(f"[tugle] falhou a geração de {hoje}: {erro}")


@asynccontextmanager
async def tempo_de_vida(app: FastAPI):
    global cliente
    cliente = httpx.AsyncClient(
        timeout=12,
        headers={"User-Agent": "Tugle/1.0", "Accept-Language": "pt-PT,pt;q=0.9"},
    )
    async with engine.begin() as conexao:
        await conexao.run_sync(Base.metadata.create_all)

    try:
        await obter_ou_criar(dt.datetime.now(LISBOA).date())
    except Exception as erro:
        print(f"[tugle] AVISO: não consegui montar o puzzle inicial: {erro}")
        print("[tugle] o servidor arranca na mesma — vê /catalogo/resumo para perceber porquê.")
    agendador.add_job(tarefa_meia_noite, CronTrigger(hour=0, minute=0, timezone=LISBOA))
    agendador.start()

    yield

    agendador.shutdown()
    await cliente.aclose()


app = FastAPI(title="Tugle", lifespan=tempo_de_vida)
app.add_middleware(
    CORSMiddleware,
    allow_origins=["https://www.tugle.pt", "https://tugle.pt", "https://tugle.onrender.com"],
    allow_methods=["GET", "POST"], allow_headers=["*"],
)


@app.middleware("http")
async def forcar_dominio_canonico(request: Request, chamar_seguinte):
    """Se alguém chega por 'tugle.pt' (sem www), manda para 'www.tugle.pt'.
    Sem isto, os dois domínios servem o mesmo site em paralelo, mas para o
    browser são origens diferentes — o localStorage (progresso, puzzles
    concluídos, sequência de dias) fica dividido consoante o domínio por
    onde se entrou, dando a sensação de que os dados "desaparecem"."""
    anfitriao = request.headers.get("host", "")
    if anfitriao.split(":")[0] == "tugle.pt":
        destino = request.url.replace(scheme="https", netloc="www.tugle.pt")
        return RedirectResponse(str(destino), status_code=301)
    return await chamar_seguinte(request)


@app.middleware("http")
async def cabecalhos_seguranca(request: Request, chamar_seguinte):
    resposta = await chamar_seguinte(request)
    resposta.headers["X-Content-Type-Options"] = "nosniff"
    resposta.headers["X-Frame-Options"] = "DENY"
    resposta.headers["Referrer-Policy"] = "strict-origin-when-cross-origin"
    return resposta

FaixasEmMemoria: dict[str, bytes] = {}


async def resolver_audio(faixa: "Faixa") -> str:
    """O link de preview da Deezer expira ao fim de algum tempo. Em vez de
    confiar no que ficou guardado no catálogo, pede sempre um link fresco
    pelo id da faixa (esse nunca muda) antes de servir o áudio."""
    try:
        r = await cliente.get(f"{DEEZER}/track/{faixa.id}")
        preview = (r.json() or {}).get("preview")
        if preview:
            return preview
    except Exception:
        pass
    return faixa.audio_origem  # recurso: usa o que estava guardado


async def obter_bytes_faixa(entrada_id: str, url: str) -> bytes:
    if entrada_id in FaixasEmMemoria:
        return FaixasEmMemoria[entrada_id]
    resposta = await cliente.get(url)
    resposta.raise_for_status()
    conteudo = resposta.content
    FaixasEmMemoria[entrada_id] = conteudo
    if len(FaixasEmMemoria) > 400:
        FaixasEmMemoria.pop(next(iter(FaixasEmMemoria)))
    return conteudo


# ---------------------------------------------------------------- rotas

PASTA = Path(__file__).parent
FICHEIRO_FRONTEND = PASTA / "tugle.html"
FICHEIRO_INICIO = PASTA / "inicio.html"
FICHEIRO_STREAM = PASTA / "stream.html"
FICHEIRO_FAVICON = PASTA / "favicon.svg"
FICHEIRO_OG_IMAGE = PASTA / "og-image.png"
FICHEIRO_ROBOTS = PASTA / "robots.txt"
FICHEIRO_SITEMAP = PASTA / "sitemap.xml"
FICHEIRO_ADS = PASTA / "ads.txt"


@app.get("/", include_in_schema=False)
async def pagina_inicial():
    """A página de entrada, com o botão Começar."""
    if FICHEIRO_INICIO.exists():
        return FileResponse(FICHEIRO_INICIO, media_type="text/html")
    return {"aviso": "coloca o inicio.html na mesma pasta do backend.py"}


@app.get("/jogar", include_in_schema=False)
async def pagina_jogo():
    """O jogo em si — quem visita esta morada não configura nada."""
    if FICHEIRO_FRONTEND.exists():
        return FileResponse(FICHEIRO_FRONTEND, media_type="text/html")
    return {"aviso": "coloca o tugle.html na mesma pasta do backend.py"}


@app.get("/jogar/modo/{origem}/{decada}", include_in_schema=False)
async def pagina_jogo_modo(origem: str, decada: str):
    """Link próprio de cada modo (ex.: /jogar/modo/nacional/1990) — serve
    a mesma página do jogo; é o próprio JavaScript que lê o caminho e
    carrega o modo certo."""
    if FICHEIRO_FRONTEND.exists():
        return FileResponse(FICHEIRO_FRONTEND, media_type="text/html")
    return {"aviso": "coloca o tugle.html na mesma pasta do backend.py"}


@app.get("/stream", include_in_schema=False)
async def pagina_stream():
    """Versão para jogar em direto na Twitch: uma palavra de cada vez,
    com deteção de acertos no chat."""
    if FICHEIRO_STREAM.exists():
        return FileResponse(FICHEIRO_STREAM, media_type="text/html")
    return {"aviso": "coloca o stream.html na mesma pasta do backend.py"}


@app.get("/favicon.svg", include_in_schema=False)
async def favicon():
    if FICHEIRO_FAVICON.exists():
        return FileResponse(FICHEIRO_FAVICON, media_type="image/svg+xml")
    raise HTTPException(404, "favicon.svg não encontrado")


@app.get("/og-image.png", include_in_schema=False)
async def og_image():
    if FICHEIRO_OG_IMAGE.exists():
        return FileResponse(FICHEIRO_OG_IMAGE, media_type="image/png")
    raise HTTPException(404, "og-image.png não encontrado")


@app.get("/robots.txt", include_in_schema=False)
async def robots():
    if FICHEIRO_ROBOTS.exists():
        return FileResponse(FICHEIRO_ROBOTS, media_type="text/plain")
    raise HTTPException(404, "robots.txt não encontrado")


@app.get("/sitemap.xml", include_in_schema=False)
async def sitemap():
    if FICHEIRO_SITEMAP.exists():
        return FileResponse(FICHEIRO_SITEMAP, media_type="application/xml")
    raise HTTPException(404, "sitemap.xml não encontrado")


@app.get("/ads.txt", include_in_schema=False)
async def ads_txt():
    if FICHEIRO_ADS.exists():
        return FileResponse(FICHEIRO_ADS, media_type="text/plain")
    raise HTTPException(404, "ads.txt não encontrado")


@app.get("/estado")
async def estado() -> dict:
    return {"servico": "Tugle", "estado": "de pé"}


@app.post("/puzzle/hoje/regenerar")
async def regenerar_hoje(_: None = Depends(exigir_chave_admin)) -> dict:
    """Força uma nova montagem do puzzle de hoje, mesmo que já exista uma
    guardada — útil sempre que o gerador de pistas ou o algoritmo melhora
    e queres que o dia de hoje reflita isso."""
    hoje = dt.datetime.now(LISBOA).date()
    return para_cliente(await gerar_e_guardar(hoje))


@app.get("/puzzle/hoje")
async def puzzle_hoje() -> dict:
    return para_cliente(await obter_ou_criar(dt.datetime.now(LISBOA).date()))


@app.get("/puzzle/hoje/modo/{origem}/{decada}")
async def puzzle_hoje_modo(origem: str, decada: str) -> dict:
    """Puzzle diário de um modo (origem e/ou década) — um só por dia,
    partilhado por toda a gente que escolher essa combinação, tal como o
    puzzle de hoje normal (mas filtrado). Nunca gerado na hora: se ainda
    não existir, é criado agora e fica gravado para o resto do dia.
    `decada` é 'todas' ou um ano tipo 1990."""
    if origem not in ("todos", "nacional", "internacional"):
        raise HTTPException(400, "origem tem de ser 'todos', 'nacional' ou 'internacional'")
    decada_int: int | None = None
    if decada != "todas":
        try:
            decada_int = int(decada)
        except ValueError:
            raise HTTPException(400, "década tem de ser 'todas' ou um ano tipo 1990")
    try:
        puzzle = await obter_ou_criar_modo(dt.datetime.now(LISBOA).date(), origem, decada_int)
    except RuntimeError as erro:
        raise HTTPException(422, str(erro))
    return para_cliente(puzzle)


@app.get("/puzzle/stream")
async def puzzle_stream(
    origem: str = "todos", decada: int | None = None, quantidade: int = 16,
    _: None = Depends(limitar_puzzle_stream),
) -> dict:
    """Só para a página de stream — gerado na hora, sempre um jogo
    diferente, nunca gravado. `quantidade` fica sempre entre 10 e 30."""
    if origem not in ("todos", "nacional", "internacional"):
        raise HTTPException(400, "origem tem de ser 'todos', 'nacional' ou 'internacional'")
    quantidade = max(10, min(30, quantidade))
    try:
        entradas = await montar_lista_stream(origem, decada, quantidade)
    except RuntimeError as erro:
        raise HTTPException(422, str(erro))
    if len(entradas) < 6:
        raise HTTPException(422, "Não consegui montar entradas suficientes com este filtro.")
    return {"entradas": [{**e, "audio": f"/audio/{e['id']}"} for e in entradas]}


@app.get("/opcoes-modo")
async def opcoes_modo() -> dict:
    """Géneros e décadas que existem mesmo no catálogo, para o seletor de
    modos nunca oferecer uma combinação que dá zero resultados."""
    async with Sessao() as sessao:
        generos = (await sessao.execute(select(Faixa.genero))).scalars().all()
        decadas = (await sessao.execute(select(Faixa.decada))).scalars().all()
    return {
        "generos": sorted({g for g in generos if g}),
        "decadas": sorted({d for d in decadas if d and d >= 1990}),
    }


@app.get("/puzzles")
async def lista_puzzles(limite: int = 90) -> list[dict]:
    async with Sessao() as sessao:
        resultado = await sessao.execute(
            select(PuzzleGuardado.data).order_by(PuzzleGuardado.data.desc())
        )
        datas = [r[0] for r in resultado.all()]
    itens = []
    for d in datas:
        try:
            data_obj = dt.date.fromisoformat(d)
        except ValueError:
            continue  # id de um modo (ex.: "2026-08-21--nacional--1990") — não é um dia de calendário, não entra no Arquivo
        itens.append({"data": d, "nome": f"Tugle de {data_obj.strftime('%d/%m/%Y')}"})
        if len(itens) >= limite:
            break
    return itens


@app.get("/puzzle/{data}")
async def puzzle_por_data(data: str) -> dict:
    try:
        d = dt.date.fromisoformat(data)
    except ValueError:
        raise HTTPException(400, "Data inválida, usa AAAA-MM-DD.")
    async with Sessao() as sessao:
        guardado = await sessao.get(PuzzleGuardado, d.isoformat())
    if not guardado:
        raise HTTPException(404, "Ainda não há puzzle guardado para esse dia.")
    conteudo = guardado.conteudo
    if puzzle_desatualizado(conteudo):
        conteudo = await gerar_e_guardar(d)
    return para_cliente(conteudo)


class DadosJogador(BaseModel):
    nome: str = "Jogador"
    total: int = 0
    sem_ajuda: int = 0
    streak: int = 0


@app.post("/jogador/{codigo}")
async def guardar_jogador(codigo: str, dados: DadosJogador, _: None = Depends(limitar_jogador)) -> dict:
    codigo = codigo.strip().upper()
    if not (4 <= len(codigo) <= 12) or not codigo.isalnum():
        raise HTTPException(400, "Código inválido — usa entre 4 e 12 letras/números.")
    nome = (dados.nome or "Jogador").strip()[:24] or "Jogador"
    async with Sessao() as sessao:
        jogador = await sessao.get(Jogador, codigo)
        if not jogador:
            jogador = Jogador(codigo=codigo)
            sessao.add(jogador)
        jogador.nome = nome
        jogador.total = max(0, dados.total)
        jogador.sem_ajuda = max(0, dados.sem_ajuda)
        jogador.streak = max(0, dados.streak)
        jogador.atualizado_em = dt.datetime.now(dt.timezone.utc).isoformat()
        await sessao.commit()
    return {"ok": True}


@app.get("/jogador/{codigo}")
async def obter_jogador(codigo: str, _: None = Depends(limitar_jogador)) -> dict:
    codigo = codigo.strip().upper()
    async with Sessao() as sessao:
        jogador = await sessao.get(Jogador, codigo)
    if not jogador:
        raise HTTPException(404, "Não existe nenhum jogador com este código.")
    return {
        "codigo": jogador.codigo,
        "nome": jogador.nome,
        "total": jogador.total,
        "sem_ajuda": jogador.sem_ajuda,
        "streak": jogador.streak,
    }


# ---------------------------------------------------------------- contas

EMAIL_REGEX = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")


class DadosRegisto(BaseModel):
    email: str
    password: str
    nome: str = "Jogador"


class DadosLogin(BaseModel):
    email: str
    password: str


def gerar_codigo() -> str:
    letras = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"  # sem 0/O/1/I, para não confundir
    return "".join(random.choice(letras) for _ in range(6))


async def criar_sessao_conta(email: str) -> str:
    token = secrets.token_urlsafe(32)
    async with Sessao() as sessao:
        sessao.add(SessaoConta(token=token, email=email, criada_em=dt.datetime.now(dt.timezone.utc).isoformat()))
        await sessao.commit()
    return token


async def resolver_conta(authorization: str | None = Header(None)) -> Conta | None:
    """Devolve a conta associada ao token, ou None sem levantar erro —
    para endpoints onde estar autenticado é opcional."""
    if not authorization or not authorization.startswith("Bearer "):
        return None
    token = authorization.removeprefix("Bearer ").strip()
    if not token:
        return None
    async with Sessao() as sessao:
        sessao_conta = await sessao.get(SessaoConta, token)
        if not sessao_conta:
            return None
        return await sessao.get(Conta, sessao_conta.email)


async def exigir_conta(authorization: str | None = Header(None)) -> Conta:
    conta = await resolver_conta(authorization)
    if not conta:
        raise HTTPException(401, "Sessão inválida ou expirada. Inicia sessão outra vez.")
    return conta


@app.post("/conta/registar")
async def registar_conta(dados: DadosRegisto, _: None = Depends(limitar_conta)) -> dict:
    email = dados.email.strip().lower()
    if not EMAIL_REGEX.match(email):
        raise HTTPException(400, "Email inválido.")
    if len(dados.password) < 6:
        raise HTTPException(400, "A password tem de ter pelo menos 6 caracteres.")
    nome = (dados.nome or "Jogador").strip()[:24] or "Jogador"
    agora = dt.datetime.now(dt.timezone.utc).isoformat()
    async with Sessao() as sessao:
        if await sessao.get(Conta, email):
            raise HTTPException(409, "Já existe uma conta com este email.")
        codigo = gerar_codigo()
        while await sessao.get(Jogador, codigo):  # (praticamente nunca colide, mas por garantia)
            codigo = gerar_codigo()
        senha_hash = bcrypt.hashpw(dados.password.encode(), bcrypt.gensalt()).decode()
        sessao.add(Conta(email=email, senha_hash=senha_hash, nome=nome, codigo=codigo, criada_em=agora))
        sessao.add(Jogador(codigo=codigo, nome=nome, atualizado_em=agora))
        await sessao.commit()
    token = await criar_sessao_conta(email)
    return {"token": token, "codigo": codigo, "nome": nome, "email": email}


@app.post("/conta/entrar")
async def entrar_conta(dados: DadosLogin, _: None = Depends(limitar_conta)) -> dict:
    email = dados.email.strip().lower()
    async with Sessao() as sessao:
        conta = await sessao.get(Conta, email)
    if not conta or not bcrypt.checkpw(dados.password.encode(), conta.senha_hash.encode()):
        raise HTTPException(401, "Email ou password incorretos.")
    token = await criar_sessao_conta(email)
    return {"token": token, "codigo": conta.codigo, "nome": conta.nome, "email": conta.email}


@app.post("/conta/sair")
async def sair_conta(authorization: str | None = Header(None)) -> dict:
    if authorization and authorization.startswith("Bearer "):
        token = authorization.removeprefix("Bearer ").strip()
        async with Sessao() as sessao:
            s = await sessao.get(SessaoConta, token)
            if s:
                await sessao.delete(s)
                await sessao.commit()
    return {"ok": True}


@app.get("/conta/eu")
async def conta_atual(conta: Conta = Depends(exigir_conta)) -> dict:
    return {"email": conta.email, "codigo": conta.codigo, "nome": conta.nome}


class DadosProgresso(BaseModel):
    conteudo: dict
    concluido: bool = False
    sem_ajuda: bool | None = None


@app.put("/conta/progresso/{puzzle_id}")
async def guardar_progresso_conta(
    puzzle_id: str,
    dados: DadosProgresso,
    conta: Conta = Depends(exigir_conta),
    _: None = Depends(limitar_progresso),
) -> dict:
    agora = dt.datetime.now(dt.timezone.utc).isoformat()
    async with Sessao() as sessao:
        registo = await sessao.get(ProgressoConta, (conta.email, puzzle_id))
        if not registo:
            registo = ProgressoConta(email=conta.email, puzzle_id=puzzle_id)
            sessao.add(registo)
        registo.conteudo = dados.conteudo
        registo.concluido = dados.concluido
        registo.sem_ajuda = dados.sem_ajuda
        registo.atualizado_em = agora
        await sessao.commit()
    return {"ok": True}


@app.get("/conta/progresso")
async def listar_progresso_conta(conta: Conta = Depends(exigir_conta)) -> list[dict]:
    """Tudo o progresso guardado nesta conta — usado para preencher um
    dispositivo novo (ou o localStorage depois de o limpares) assim que
    inicias sessão."""
    async with Sessao() as sessao:
        resultado = await sessao.execute(
            select(ProgressoConta).where(ProgressoConta.email == conta.email)
        )
        registos = resultado.scalars().all()
    return [
        {
            "puzzle_id": r.puzzle_id,
            "conteudo": r.conteudo,
            "concluido": r.concluido,
            "sem_ajuda": r.sem_ajuda,
            "atualizado_em": r.atualizado_em,
        }
        for r in registos
    ]


@app.get("/catalogo/resumo")
async def catalogo_resumo() -> dict:
    async with Sessao() as sessao:
        todas = list((await sessao.execute(select(Faixa))).scalars().all())
    por_genero: dict[str, int] = {}
    por_artista: dict[str, int] = {}
    for f in todas:
        chave = f.genero or "sem género"
        por_genero[chave] = por_genero.get(chave, 0) + 1
        por_artista[f.artista] = por_artista.get(f.artista, 0) + 1

    artistas_todos = set(ARTISTAS) | set(ARTISTAS_INTERNACIONAIS)
    artistas_com_faixas = {normalizar(a) for a in por_artista}
    artistas_por_explorar = sorted(
        a for a in artistas_todos if normalizar(a) not in artistas_com_faixas
    )

    return {
        "total": len(todas),
        "por_genero": por_genero,
        "por_artista": dict(sorted(por_artista.items(), key=lambda x: -x[1])),
        "artistas_com_faixas": len(por_artista),
        "artistas_por_explorar": artistas_por_explorar,
    }


@app.post("/catalogo/limpar")
async def catalogo_limpar(artista: str | None = None, _: None = Depends(exigir_chave_admin)) -> dict:
    """Sem parâmetro: apaga faixas de artistas que já não estão em ARTISTAS.
    Com ?artista=Nome: apaga TODAS as faixas guardadas desse nome, mesmo que
    ainda esteja na lista — útil quando a Deezer confundiu com um homónimo
    (ex.: /catalogo/limpar?artista=Agir depois de corrigir o id em IDS_ARTISTA_DEEZER)."""
    async with Sessao() as sessao:
        todas = list((await sessao.execute(select(Faixa))).scalars().all())
        if artista:
            alvo = normalizar(artista)
            removidas = [f for f in todas if normalizar(f.artista) == alvo]
        else:
            artistas_atuais = {normalizar(a) for a in ARTISTAS} | {normalizar(a) for a in ARTISTAS_INTERNACIONAIS}
            removidas = [f for f in todas if normalizar(f.artista) not in artistas_atuais]
        for f in removidas:
            await sessao.delete(f)
        await sessao.commit()
    return {"removidas": len(removidas), "restantes": len(todas) - len(removidas)}


@app.get("/deezer/{caminho:path}")
async def deezer_proxy(caminho: str, request: Request):
    """Usado pelo editor para pesquisar músicas a acrescentar ao catálogo."""
    if ".." in caminho:
        raise HTTPException(400, "Caminho inválido.")
    r = await cliente.get(f"{DEEZER}/{caminho}", params=dict(request.query_params))
    return Response(r.content, media_type="application/json", status_code=r.status_code)


@app.get("/itunes")
async def itunes_proxy(request: Request):
    params = {"media": "music", "entity": "song", "country": "PT", "limit": "24",
              **dict(request.query_params)}
    if not params.get("term"):
        raise HTTPException(400, "Falta o termo de pesquisa.")
    r = await cliente.get("https://itunes.apple.com/search", params=params)
    return Response(r.content, media_type="application/json", status_code=r.status_code)


@app.get("/audio/{entrada_id}")
async def audio(entrada_id: str, request: Request):
    async with Sessao() as sessao:
        faixa = await sessao.get(Faixa, entrada_id)
    if not faixa:
        raise HTTPException(404, "Sem áudio para esta entrada.")

    try:
        url_fresca = await resolver_audio(faixa)
        conteudo = await obter_bytes_faixa(entrada_id, url_fresca)
    except httpx.HTTPError:
        raise HTTPException(502, "A Deezer não devolveu o excerto.")

    tamanho = len(conteudo)
    cabecalhos = {"Accept-Ranges": "bytes", "Cache-Control": "public, max-age=21600"}

    intervalo = request.headers.get("range")
    if intervalo:
        m = re.match(r"bytes=(\d*)-(\d*)", intervalo)
        inicio = int(m.group(1)) if m and m.group(1) else 0
        fim = min(int(m.group(2)), tamanho - 1) if m and m.group(2) else tamanho - 1
        pedaco = conteudo[inicio:fim + 1]
        cabecalhos["Content-Range"] = f"bytes {inicio}-{fim}/{tamanho}"
        cabecalhos["Content-Length"] = str(len(pedaco))
        return Response(pedaco, status_code=206, media_type="audio/mpeg", headers=cabecalhos)

    cabecalhos["Content-Length"] = str(tamanho)
    return Response(conteudo, media_type="audio/mpeg", headers=cabecalhos)
