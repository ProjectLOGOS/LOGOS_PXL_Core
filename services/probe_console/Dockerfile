FROM python:3.11-slim
WORKDIR /app
COPY . /app
RUN pip install fastapi uvicorn requests pydantic --no-cache-dir
ENV ARCHON_URL=http://archon:8000 LOGOS_URL=http://logos-api:8090 EXEC_URL=http://executor:8000
CMD ["python","-m","uvicorn","app:app","--host","0.0.0.0","--port","8000"]