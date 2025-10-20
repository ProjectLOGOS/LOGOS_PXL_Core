# logos_agi_v1/subsystems/thonoc/Dockerfile

FROM python:3.11-slim

# Set working directory
WORKDIR /app

# Install system dependencies for logical reasoning and theorem proving
RUN apt-get update && apt-get install -y \
    gcc \
    g++ \
    python3-dev \
    libssl-dev \
    libffi-dev \
    build-essential \
    git \
    wget \
    curl \
    z3 \
    && rm -rf /var/lib/apt/lists/*

# Copy requirements first for better Docker layer caching
COPY requirements.txt .

# Install Python dependencies
RUN pip install --no-cache-dir --upgrade pip && \
    pip install --no-cache-dir -r requirements.txt

# Create necessary directories
RUN mkdir -p /app/logs /app/data /app/proofs /app/axioms

# Copy core modules and application code
COPY core/ ./core/
COPY subsystems/thonoc/ ./
COPY shared/ ./shared/ 2>/dev/null || true

# Create non-root user for security
RUN useradd --create-home --shell /bin/bash thonoc && \
    chown -R thonoc:thonoc /app

# Switch to non-root user
USER thonoc

# Set environment variables
ENV PYTHONPATH=/app
ENV PYTHONUNBUFFERED=1
ENV WORKER_TYPE=thonoc
ENV LOG_LEVEL=INFO
ENV Z3_LIBRARY_PATH=/usr/lib/x86_64-linux-gnu

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=10s --retries=3 \
    CMD python -c "import z3; print('Z3 theorem prover OK')" || exit 1

# Default command
CMD ["python", "thonoc_worker.py"]
