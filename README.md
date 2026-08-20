# Tugle

Palavras cruzadas diárias com música portuguesa. Ouves um excerto, escreves o que reconheces, as respostas cruzam-se numa grelha nova a cada meia-noite.

**→ [Ver o site](#)** — atualiza este link depois do deploy na Render.

---

## Como é

- **Início** — ecrã de entrada, só com o botão Começar.
- **Jogar** — a grelha do dia, com um disco de vinil a tocar o excerto e uma pista de texto (artista, década, género) para cada entrada.
- **Editor** — pesquisa músicas na Deezer/iTunes e monta puzzles à mão.
- **Check** — três níveis de ajuda (Letra / Palavra / Puzzle inteiro).
- **Arquivo** — dias anteriores, num painel lateral.

---

## Por dentro

Diferente do Tierlist-Cubinho, isto **não é estático** — precisa de um servidor Python a correr a sério, por três razões: os links de excerto da Deezer expiram (o servidor pede um link fresco a cada reprodução), a grelha nova à meia-noite precisa de algo a correr sozinho, e o catálogo de músicas cresce ao longo do tempo numa base de dados.

| | |
|---|---|
| **`backend.py`** | FastAPI + SQLite (SQLAlchemy async). Gera o puzzle diário, mantém o catálogo, serve o áudio e a própria página. |
| **`tugle.html`** | O jogo — HTML/CSS/JS num único ficheiro, sem build step. |
| **`inicio.html`** | Página de entrada. |
| **Catálogo** | Tabela `faixas`, guardada em `tugle.db`, nunca esvaziada — só marca quando uma música já saiu, para não repetir antes de 45 dias. |
| **Artistas** | Lista fixa em `backend.py` (`ARTISTAS`), só cantores em português, a maioria bem conhecidos. |

## Correr localmente

```bash
python3.12 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
fastapi dev backend.py
```

Abre `http://localhost:8000`. Na primeira vez demora um pouco mais — o servidor vai à Deezer construir o catálogo inicial antes de responder.

## Publicar

O GitHub Pages não serve para isto (não corre Python). Este repositório liga-se à [Render](https://render.com):

- Build: `pip install -r requirements.txt`
- Start: `uvicorn backend:app --host 0.0.0.0 --port $PORT`
- Disco persistente montado, com a variável de ambiente `DATABASE_URL` a apontar para lá — sem isso, o catálogo desaparece a cada deploy.

## Adicionar ou remover artistas

A lista está em `backend.py`, na variável `ARTISTAS`. Só nomes que cantem predominantemente em português — o resto do sistema (pesquisa de faixas, catálogo, geração da grelha) reage sozinho a qualquer alteração.

---

Feito com AI. Ideias, correções, ou problemas: [**@tiagodlcantante**](https://instagram.com/tiagodlcantante) no Instagram.
