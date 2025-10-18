FROM python:3.11-slim
WORKDIR /app
COPY . /app
RUN pip install fastapi uvicorn requests pydantic --no-cache-dir
ENV TOOL_ROUTER_URL=http://tool-router:8000
CMD ["python","-m","uvicorn","app:app","--host","0.0.0.0","--port","8000"]
