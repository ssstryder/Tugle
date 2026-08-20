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
import unicodedata
from contextlib import asynccontextmanager
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit
from zoneinfo import ZoneInfo

import httpx
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from apscheduler.triggers.cron import CronTrigger
from fastapi import FastAPI, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, Response
from sqlalchemy import Integer, String, select
from sqlalchemy import JSON
from sqlalchemy.ext.asyncio import AsyncSession, async_sessionmaker, create_async_engine
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
ENTRADAS_POR_PUZZLE = 16
# A Deezer recorta os 30s de antevisão a começar algures na música, muitas
# vezes ainda em desvanecimento/intro. Saltar uns segundos costuma aproximar
# do refrão — não há forma de o garantir sem analisar o áudio a sério.
INICIO_EXCERTO_SEGUNDOS = 6

# ---------------------------------------------------------------- artistas

ARTISTAS = [
    # fado
    "Amália Rodrigues", "Mariza", "Carminho", "Ana Moura", "Camané",
    "Gisela João", "Cuca Roseta", "Raquel Tavares", "Sara Correia",
    # rock e indie
    "Zeca Afonso", "Sérgio Godinho", "Rui Veloso",
    "Xutos & Pontapés", "GNR", "Ornatos Violeta",
    "Pedro Abrunhosa", "Linda Martini",
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
    "Salvador Sobral", "Conan Osíris", "Bárbara Tinoco", "Diogo Piçarra",
    "Aurea", "Ana Bacalhau", "Miguel Araújo", "David Carreira",
    "Fernando Daniel", "Marisa Liz", "Miguel Gameiro", "Cláudia Pascoal",
    "Iolanda", "Bárbara Bandeira", "Blaya", "Mafalda Veiga", "Rita Guerra",
    "Van Zee", "Carolina Deslandes", "MARO", "NAPA", "Vizinhos",
    "Soraia Ramos", "Pedro Mafama",
    # pimba (muito popular em Portugal, apesar de tudo)
    "Quim Barreiros", "Tony Carreira", "Emanuel", "Ágata", "Ana Malhoa",
    "Marco Paulo",
]


def artistas_do_dia(data: dt.date, quantos: int) -> list[str]:
    aleatorio = random.Random(data.isoformat())
    return aleatorio.sample(ARTISTAS, min(quantos, len(ARTISTAS)))


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


engine = create_async_engine(BASE_DE_DADOS, connect_args=_connect_args)
Sessao = async_sessionmaker(engine, expire_on_commit=False)


# ---------------------------------------------------------------- Deezer

cliente: httpx.AsyncClient | None = None


# Alguns nomes são ambíguos na pesquisa da Deezer (há homónimos noutros
# países) — para estes, usa-se sempre o id exato em vez de confiar na busca.
IDS_ARTISTA_DEEZER: dict[str, int] = {
    "Agir": 665993,  # o português (Bernardo Costa) — não o rapper alemão do mesmo nome
}


async def explorar_artista(artista: str) -> list[dict]:
    """Até 3 faixas com excerto disponível para um artista."""
    id_conhecido = IDS_ARTISTA_DEEZER.get(artista)
    if id_conhecido:
        artista_id = id_conhecido
    else:
        try:
            r = await cliente.get(f"{DEEZER}/search/artist", params={"q": artista, "limit": 1})
            achados = (r.json() or {}).get("data") or []
        except Exception as erro:
            print(f"[tugle]   {artista}: falhou a pesquisa de artista ({erro})")
            return []
        if not achados:
            print(f"[tugle]   {artista}: a Deezer não encontrou este artista")
            return []
        artista_id = achados[0]["id"]

    try:
        r = await cliente.get(f"{DEEZER}/artist/{artista_id}/top", params={"limit": 20})
        topo = (r.json() or {}).get("data") or []
    except Exception as erro:
        print(f"[tugle]   {artista}: falhou a lista de faixas ({erro})")
        return []

    faixas = []
    for faixa in topo:
        if not faixa.get("preview"):
            continue
        faixas.append({
            "id": str(faixa["id"]),
            "titulo": limpar_titulo(faixa.get("title_short") or faixa.get("title", "")),
            "artista": faixa.get("artist", {}).get("name", artista),
            "album": faixa.get("album", {}).get("title", ""),
            "album_id": faixa.get("album", {}).get("id"),
            "capa": faixa.get("album", {}).get("cover_medium", ""),
            "audio": faixa["preview"],
        })
        if len(faixas) >= 12:
            break
    if not faixas:
        print(f"[tugle]   {artista}: encontrado, mas nenhuma faixa tem excerto (preview vazio)")
    return faixas


async def genero_e_decada(album_id) -> tuple[str, int | None]:
    if not album_id:
        return "", None
    try:
        r = await cliente.get(f"{DEEZER}/album/{album_id}")
        d = r.json() or {}
        genero = ((d.get("genres") or {}).get("data") or [{}])[0].get("name", "")
        lancamento = d.get("release_date", "") or ""
        decada = int(lancamento[:3] + "0") if len(lancamento) >= 4 and lancamento[:4].isdigit() else None
        return genero, decada
    except Exception:
        return "", None


async def garantir_catalogo(minimo: int) -> None:
    async with Sessao() as sessao:
        total = len((await sessao.execute(select(Faixa.id))).all())
        if total >= minimo:
            return

        print(f"[tugle] catálogo tem {total} faixas, a construir até {minimo}…")
        for artista in artistas_do_dia(dt.date.today(), len(ARTISTAS)):
            if total >= minimo:
                break
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

def pista_para(faixa: "Faixa") -> str:
    partes = [f"Música de {faixa.artista}."]
    if faixa.decada:
        partes.append(f"Da década de {faixa.decada}.")
    if faixa.genero:
        partes.append(f"Género: {faixa.genero}.")
    return " ".join(partes)


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

    # títulos muito compridos (30+ letras) costumam ser metadados mal limpos
    # (nomes de compilação, featurings) e fazem a grelha esticar-se demais
    candidatas = [f for f in candidatas if 3 <= len(normalizar(f.titulo)) <= 14]

    # ignora sempre quem já não está na lista ARTISTAS — evita que alguém
    # removido continue a aparecer só porque ficou guardado no catálogo
    artistas_atuais = {normalizar(a) for a in ARTISTAS}
    candidatas = [f for f in candidatas if normalizar(f.artista) in artistas_atuais]

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

    entradas = [{
        "id": f.id, "resposta": f.titulo, "titulo": f.titulo, "artista": f.artista,
        "capa": f.capa, "genero": f.genero, "decada": f.decada,
        "pista": pista_para(f), "inicio": INICIO_EXCERTO_SEGUNDOS,
    } for f in candidatas]

    grelha = gerar_grelha(entradas)
    if grelha.get("erro") or len(grelha.get("colocadas", [])) < 5:
        raise RuntimeError(f"Não consegui montar puzzle de {data} com o catálogo atual.")

    ids_colocados = {c["entradaId"] for c in grelha["colocadas"]}
    entradas_finais = [e for e in entradas if e["id"] in ids_colocados]

    return {
        "id": data.isoformat(),
        "nome": f"Tugle de {data.strftime('%d/%m/%Y')}",
        "data": data.isoformat(),
        "entradas": entradas_finais,
        "grelha": {
            "linhas": grelha["linhas"], "colunas": grelha["colunas"],
            "colocadas": grelha["colocadas"],
        },
    }


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
    for c in grelha.get("colocadas", []):
        if c.get("entradaId") not in ids_validos:
            return True
        comprimento = len(c.get("palavra", ""))
        if c.get("dir") == "down" and c.get("r", 0) + comprimento > linhas:
            return True
        if c.get("dir") == "across" and c.get("c", 0) + comprimento > colunas:
            return True
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
    cliente = httpx.AsyncClient(timeout=12, headers={"User-Agent": "Tugle/1.0"})
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
FICHEIRO_FAVICON = PASTA / "favicon.svg"


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


@app.get("/favicon.svg", include_in_schema=False)
async def favicon():
    if FICHEIRO_FAVICON.exists():
        return FileResponse(FICHEIRO_FAVICON, media_type="image/svg+xml")
    raise HTTPException(404, "favicon.svg não encontrado")


@app.get("/estado")
async def estado() -> dict:
    return {"servico": "Tugle", "estado": "de pé"}


@app.post("/puzzle/hoje/regenerar")
async def regenerar_hoje() -> dict:
    """Força uma nova montagem do puzzle de hoje, mesmo que já exista uma
    guardada — útil sempre que o gerador de pistas ou o algoritmo melhora
    e queres que o dia de hoje reflita isso."""
    hoje = dt.datetime.now(LISBOA).date()
    return para_cliente(await gerar_e_guardar(hoje))


@app.get("/puzzle/hoje")
async def puzzle_hoje() -> dict:
    return para_cliente(await obter_ou_criar(dt.datetime.now(LISBOA).date()))


@app.get("/puzzles")
async def lista_puzzles(limite: int = 90) -> list[dict]:
    async with Sessao() as sessao:
        resultado = await sessao.execute(
            select(PuzzleGuardado.data).order_by(PuzzleGuardado.data.desc()).limit(limite)
        )
        datas = [r[0] for r in resultado.all()]
    return [
        {"data": d, "nome": f"Tugle de {dt.date.fromisoformat(d).strftime('%d/%m/%Y')}"}
        for d in datas
    ]


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
    return para_cliente(guardado.conteudo)


@app.get("/catalogo/resumo")
async def catalogo_resumo() -> dict:
    async with Sessao() as sessao:
        todas = list((await sessao.execute(select(Faixa))).scalars().all())
    por_genero: dict[str, int] = {}
    for f in todas:
        chave = f.genero or "sem género"
        por_genero[chave] = por_genero.get(chave, 0) + 1
    return {"total": len(todas), "por_genero": por_genero}


@app.post("/catalogo/limpar")
async def catalogo_limpar(artista: str | None = None) -> dict:
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
            artistas_atuais = {normalizar(a) for a in ARTISTAS}
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
