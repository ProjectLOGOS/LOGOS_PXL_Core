FROM python:3.11-slim
WORKDIR /app
COPY . /app
RUN apt-get update && apt-get install -y libopenblas-base && rm -rf /var/lib/apt/lists/*
RUN pip install fastapi uvicorn pydantic sentence-transformers scikit-learn --no-cache-dir
ENV SENTENCE_TRANSFORMERS_HOME=/root/.cache/sentence_transformers
CMD ["python","-m","uvicorn","app:app","--host","0.0.0.0","--port","8000"]
