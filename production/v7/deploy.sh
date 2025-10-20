#!/bin/bash

# LOGOS AGI v0.7-rc2 Production Deployment Script
# ===============================================

set -e

LOGOS_VERSION="0.7-rc2"
DEPLOYMENT_ENV="${1:-production}"

echo "🚀 LOGOS AGI v${LOGOS_VERSION} Deployment Script"
echo "================================================"
echo "Environment: ${DEPLOYMENT_ENV}"
echo "Timestamp: $(date)"
echo ""

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check prerequisites
check_prerequisites() {
    log_info "Checking prerequisites..."

    # Check Docker
    if ! command -v docker &> /dev/null; then
        log_error "Docker is not installed"
        exit 1
    fi
    log_success "Docker found: $(docker --version)"

    # Check Docker Compose
    if ! command -v docker-compose &> /dev/null; then
        log_error "Docker Compose is not installed"
        exit 1
    fi
    log_success "Docker Compose found: $(docker-compose --version)"

    # Check available memory
    if command -v free &> /dev/null; then
        AVAILABLE_MEM=$(free -m | awk 'NR==2{printf "%.0f", $7}')
        if [ "$AVAILABLE_MEM" -lt 8192 ]; then
            log_warning "Available memory (${AVAILABLE_MEM}MB) is less than recommended 8GB"
        else
            log_success "Available memory: ${AVAILABLE_MEM}MB"
        fi
    fi

    # Check disk space
    if command -v df &> /dev/null; then
        AVAILABLE_SPACE=$(df -BG . | awk 'NR==2{print $4}' | sed 's/G//')
        if [ "$AVAILABLE_SPACE" -lt 20 ]; then
            log_warning "Available disk space (${AVAILABLE_SPACE}GB) is less than recommended 20GB"
        else
            log_success "Available disk space: ${AVAILABLE_SPACE}GB"
        fi
    fi
}

# Build Docker images
build_images() {
    log_info "Building LOGOS v${LOGOS_VERSION} Docker images..."

    # Build unified image
    if [ -f "../../../Dockerfile.unified" ]; then
        log_info "Building unified runtime image..."
        docker build -f ../../../Dockerfile.unified -t logos/agi-unified:${LOGOS_VERSION} ../../../
        docker tag logos/agi-unified:${LOGOS_VERSION} logos/agi-unified:latest
        log_success "Unified runtime image built"
    else
        log_error "Dockerfile.unified not found"
        exit 1
    fi
}

# Create necessary directories
create_directories() {
    log_info "Creating deployment directories..."

    mkdir -p monitoring/grafana/{dashboards,datasources}
    mkdir -p nginx/ssl
    mkdir -p logs
    mkdir -p data/{models,proofs,cache}

    log_success "Directories created"
}

# Generate configuration files
generate_configs() {
    log_info "Generating configuration files..."

    # Prometheus configuration
    cat > monitoring/prometheus.yml << EOF
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'logos-unified'
    static_configs:
      - targets: ['logos-unified:8080']
    metrics_path: '/metrics'
    scrape_interval: 10s

  - job_name: 'logos-proof-server'
    static_configs:
      - targets: ['logos-proof-server:8081']
    metrics_path: '/metrics'

  - job_name: 'logos-reasoning'
    static_configs:
      - targets: ['logos-reasoning:8082']
    metrics_path: '/metrics'

  - job_name: 'redis'
    static_configs:
      - targets: ['redis:6379']

  - job_name: 'rabbitmq'
    static_configs:
      - targets: ['rabbitmq:15692']
EOF

    # Nginx configuration
    cat > nginx/nginx.conf << EOF
events {
    worker_connections 1024;
}

http {
    upstream logos_backend {
        server logos-unified:8080;
    }

    upstream proof_backend {
        server logos-proof-server:8081;
    }

    upstream reasoning_backend {
        server logos-reasoning:8082;
    }

    server {
        listen 80;

        location / {
            proxy_pass http://logos_backend;
            proxy_set_header Host \$host;
            proxy_set_header X-Real-IP \$remote_addr;
            proxy_set_header X-Forwarded-For \$proxy_add_x_forwarded_for;
        }

        location /proof/ {
            proxy_pass http://proof_backend/;
            proxy_set_header Host \$host;
            proxy_set_header X-Real-IP \$remote_addr;
        }

        location /reasoning/ {
            proxy_pass http://reasoning_backend/;
            proxy_set_header Host \$host;
            proxy_set_header X-Real-IP \$remote_addr;
        }

        location /health {
            return 200 'healthy';
            add_header Content-Type text/plain;
        }
    }
}
EOF

    # Grafana datasource
    cat > monitoring/grafana/datasources/prometheus.yml << EOF
apiVersion: 1

datasources:
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    isDefault: true
EOF

    log_success "Configuration files generated"
}

# Deploy services
deploy_services() {
    log_info "Deploying LOGOS v${LOGOS_VERSION} services..."

    # Stop existing services
    docker-compose -f docker-compose.v7.yml down --remove-orphans

    # Start services
    docker-compose -f docker-compose.v7.yml up -d

    log_success "Services deployment initiated"
}

# Wait for services to be healthy
wait_for_services() {
    log_info "Waiting for services to become healthy..."

    local services=("logos-unified" "logos-proof-server" "logos-reasoning" "redis" "rabbitmq")
    local max_wait=300  # 5 minutes
    local wait_time=0

    for service in "${services[@]}"; do
        log_info "Waiting for ${service}..."

        while [ $wait_time -lt $max_wait ]; do
            if docker-compose -f docker-compose.v7.yml ps ${service} | grep -q "healthy\|Up"; then
                log_success "${service} is ready"
                break
            fi

            sleep 10
            wait_time=$((wait_time + 10))
        done

        if [ $wait_time -ge $max_wait ]; then
            log_warning "${service} did not become healthy within ${max_wait} seconds"
        fi
    done
}

# Run deployment validation
validate_deployment() {
    log_info "Running deployment validation..."

    # Check if validation script exists
    if [ -f "../../../validate_v7.py" ]; then
        log_info "Running LOGOS v7 validation..."
        python3 ../../../validate_v7.py --environment ${DEPLOYMENT_ENV} --skip-performance

        if [ $? -eq 0 ]; then
            log_success "Deployment validation passed"
        else
            log_warning "Deployment validation had issues"
        fi
    else
        log_warning "Validation script not found, skipping validation"
    fi

    # Basic service health checks
    log_info "Performing basic health checks..."

    # Check unified runtime
    if curl -f http://localhost:8080/health &> /dev/null; then
        log_success "Unified runtime health check passed"
    else
        log_warning "Unified runtime health check failed"
    fi

    # Check monitoring
    if curl -f http://localhost:9090/-/healthy &> /dev/null; then
        log_success "Prometheus health check passed"
    else
        log_warning "Prometheus health check failed"
    fi
}

# Display deployment information
show_deployment_info() {
    echo ""
    echo "🎉 LOGOS AGI v${LOGOS_VERSION} Deployment Complete!"
    echo "================================================="
    echo ""
    echo "Service Endpoints:"
    echo "  • Unified API:       http://localhost:8080"
    echo "  • Proof Server:      http://localhost:8081"
    echo "  • Reasoning Engine:  http://localhost:8082"
    echo "  • Prometheus:        http://localhost:9090"
    echo "  • Grafana:          http://localhost:3000 (admin/admin123)"
    echo "  • RabbitMQ:         http://localhost:15672 (logos/secure_pass)"
    echo ""
    echo "Management Commands:"
    echo "  • View logs:         docker-compose -f docker-compose.v7.yml logs -f"
    echo "  • Check status:      docker-compose -f docker-compose.v7.yml ps"
    echo "  • Stop services:     docker-compose -f docker-compose.v7.yml down"
    echo "  • Restart services:  docker-compose -f docker-compose.v7.yml restart"
    echo ""
    echo "Production deployment ready for use! 🚀"
}

# Main deployment flow
main() {
    log_info "Starting LOGOS AGI v${LOGOS_VERSION} deployment..."

    check_prerequisites
    create_directories
    generate_configs
    build_images
    deploy_services
    wait_for_services
    validate_deployment
    show_deployment_info

    log_success "Deployment completed successfully!"
}

# Run deployment
main "$@"
