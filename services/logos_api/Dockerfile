FROM python:3.11-slim
WORKDIR /app

# minimal OS deps for curl-based healthchecks from other images
RUN apt-get update && apt-get install -y curl && rm -rf /var/lib/apt/lists/*

COPY requirements.txt /app/requirements.txt
RUN pip install --no-cache-dir -r /app/requirements.txt

COPY logos_core /app/logos_core
COPY configs /app/configs
COPY audit /app/audit

ENV PYTHONPATH=/app
EXPOSE 8090

HEALTHCHECK --interval=15s --timeout=5s --retries=5 CMD curl -f http://localhost:8090/health || exit 1

CMD ["python","-m","uvicorn","logos_core.server:app","--host","0.0.0.0","--port","8090"]