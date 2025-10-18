FROM python:3.11-slim
WORKDIR /app

RUN apt-get update && apt-get install -y ca-certificates curl && rm -rf /var/lib/apt/lists/*

COPY services/interactive_chat/requirements.txt /app/requirements.txt
RUN pip install --no-cache-dir -r /app/requirements.txt

COPY services/interactive_chat /app/services/interactive_chat

ENV PYTHONPATH=/app

EXPOSE 8080

HEALTHCHECK --interval=15s --timeout=5s --retries=5 CMD curl -fsS http://localhost:8080/health || exit 1

CMD ["python","-m","uvicorn","services.interactive_chat.app:app","--host","0.0.0.0","--port","8080"]