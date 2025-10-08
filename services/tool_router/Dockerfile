FROM python:3.11-slim
WORKDIR /app

# Why: ensure prod image contains rate limit envs by default.
RUN apt-get update && apt-get install -y ca-certificates curl && rm -rf /var/lib/apt/lists/*

COPY services/tool_router/requirements.txt /app/requirements.txt
RUN pip install --no-cache-dir -r /app/requirements.txt

COPY services/tool_router /app/services/tool_router

ENV PYTHONPATH=/app
ENV RATE_LIMIT_REQS=100 RATE_LIMIT_WINDOW_SECS=60

EXPOSE 8071

HEALTHCHECK --interval=15s --timeout=5s --retries=5 CMD curl -fsS http://localhost:8071/health || exit 1

CMD ["python","-m","uvicorn","services.tool_router.app:app","--host","0.0.0.0","--port","8071"]