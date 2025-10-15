FROM python:3.11-slimFROM python:3.11-slim

WORKDIR /appWORKDIR /app

COPY . /appCOPY . /app

# coreRUN pip install fastapi uvicorn aio-pika requests --no-cache-dir

RUN pip install fastapi uvicorn aio-pika requests --no-cache-dirCMD ["python","-m","uvicorn","app:app","--host","0.0.0.0","--port","8000"]

# TELOS stack
RUN pip install pmdarima arch pymc --no-cache-dir || true
RUN pip install causal-learn --no-cache-dir || true
# TETRAGNOS stack
RUN pip install scikit-learn umap-learn sentence-transformers --no-cache-dir || true
# THONOC stack
RUN pip install z3-solver sympy networkx --no-cache-dir || true
ENV V4PATH=/v4
CMD ["python","-m","uvicorn","app:app","--host","0.0.0.0","--port","8000"]