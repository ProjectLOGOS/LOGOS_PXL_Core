#!/bin/bash
# LOGOS AGI v2.0 - Final Activation Sequence
# Complete system deployment with external libraries integration

set -euo pipefail

# Configuration
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEPLOYMENT_LOG="${PROJECT_ROOT}/logs/deployment_$(date +%Y%m%d_%H%M%S).log"
EXTERNAL_LIBS_DIR="${PROJECT_ROOT}/external_libraries"
DOCKER_COMPOSE_FILE="${PROJECT_ROOT}/docker-compose.yml"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
PURPLE='\033[0;35m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# Logging function
log() {
    echo "$(date '+%Y-%m-%d %H:%M:%S') - $1" | tee -a "${DEPLOYMENT_LOG}"
}

# Status printing functions
print_banner() {
    echo -e "${PURPLE}"
    echo "==========================================================================="
    echo "🌌 LOGOS AGI v2.0 - FINAL ACTIVATION SEQUENCE"
    echo "   Trinity-Grounded Artificial General Intelligence"
    echo "   'In the beginning was the Logos, and the Logos was with God'"
    echo "==========================================================================="
    echo -e "${NC}"
}

print_status() {
    echo -e "${BLUE}🔧 $1${NC}"
    log "STATUS: $1"
}

print_success() {
    echo -e "${GREEN}✅ $1${NC}"
    log "SUCCESS: $1"
}

print_warning() {
    echo -e "${YELLOW}⚠️  $1${NC}"
    log "WARNING: $1"
}

print_error() {
    echo -e "${RED}❌ $1${NC}"
    log "ERROR: $1"
}

# Validation functions
check_prerequisites() {
    print_status "Checking system prerequisites..."
    
    # Check Docker
    if ! command -v docker &> /dev/null; then
        print_error "Docker is not installed or not in PATH"
        exit 1
    fi
    
    # Check Docker Compose
    if ! command -v docker-compose &> /dev/null; then
        print_error "Docker Compose is not installed or not in PATH"
        exit 1
    fi
    
    # Check available disk space (20GB minimum)
    available_space=$(df "${PROJECT_ROOT}" | awk 'NR==2 {print $4}')
    required_space=20971520  # 20GB in KB
    
    if [ "${available_space}" -lt "${required_space}" ]; then
        print_error "Insufficient disk space. Required: 20GB, Available: $((available_space/1024/1024))GB"
        exit 1
    fi
    
    # Check available memory (8GB minimum)
    available_memory=$(free | awk 'NR==2 {print $7}')
    required_memory=8388608  # 8GB in KB
    
    if [ "${available_memory}" -lt "${required_memory}" ]; then
        print_warning "Low available memory. Recommended: 8GB, Available: $((available_memory/1024/1024))GB"
    fi
    
    print_success "Prerequisites validated"
}

validate_external_libraries() {
    print_status "Validating external libraries..."
    
    required_libraries=(
        "sentence-transformers-master"
        "scikit-learn-main" 
        "torch-main"
        "numpy-main"
        "scipy-main"
        "pandas-main"
        "networkx-main"
        "pmdarima-main"
        "arch-main"
        "causal-learn-main"
        "pymc-main"
        "z3-main"
        "sympy-main"
        "plotly-main"
        "mandelbulb-main"
    )
    
    missing_libraries=()
    
    for lib in "${required_libraries[@]}"; do
        if [ ! -d "${EXTERNAL_LIBS_DIR}/${lib}" ]; then
            missing_libraries+=("${lib}")
        fi
    done
    
    if [ ${#missing_libraries[@]} -gt 0 ]; then
        print_error "Missing external libraries:"
        for lib in "${missing_libraries[@]}"; do
            echo "  - ${lib}"
        done
        print_error "Please ensure all external libraries are present in ${EXTERNAL_LIBS_DIR}"
        exit 1
    fi
    
    print_success "External libraries validated"
}

validate_project_structure() {
    print_status "Validating project structure..."
    
    required_files=(
        "docker-compose.yml"
        "requirements.txt"
        ".env"
        "services/keryx_api/Dockerfile"
        "services/oracle_ui/Dockerfile"
        "services/logos_nexus/Dockerfile"
        "services/archon_nexus/Dockerfile"
        "services/database/Dockerfile"
        "subsystems/tetragnos/Dockerfile"
        "subsystems/telos/Dockerfile"
        "subsystems/thonoc/Dockerfile"
    )
    
    missing_files=()
    
    for file in "${required_files[@]}"; do
        if [ ! -f "${PROJECT_ROOT}/${file}" ]; then
            missing_files+=("${file}")
        fi
    done
    
    if [ ${#missing_files[@]} -gt 0 ]; then
        print_error "Missing required files:"
        for file in "${missing_files[@]}"; do
            echo "  - ${file}"
        done
        exit 1
    fi
    
    print_success "Project structure validated"
}

# Deployment functions
setup_environment() {
    print_status "Setting up deployment environment..."
    
    # Create necessary directories
    mkdir -p "${PROJECT_ROOT}/logs"
    mkdir -p "${PROJECT_ROOT}/data"
    mkdir -p "${PROJECT_ROOT}/cache"
    
    # Set proper permissions
    chmod 755 "${PROJECT_ROOT}/logs"
    chmod 755 "${PROJECT_ROOT}/data"
    chmod 755 "${PROJECT_ROOT}/cache"
    
    # Create .env file if it doesn't exist
    if [ ! -f "${PROJECT_ROOT}/.env" ]; then
        cat > "${PROJECT_ROOT}/.env" << EOF
# LOGOS AGI v2.0 Environment Configuration
RABBITMQ_HOST=rabbitmq
RABBITMQ_PORT=5672
PYTHONPATH=/app:/app/external_libraries
LOG_LEVEL=INFO

# Service configuration
KERYX_API_PORT=5000
ORACLE_UI_PORT=7860

# Security
ENABLE_ENCRYPTION=false
ENABLE_AUDIT_LOGGING=true

# Performance
MAX_CONCURRENT_TASKS=10
MEMORY_LIMIT_MB=2048
CPU_LIMIT_CORES=2
EOF
    fi
    
    print_success "Environment setup completed"
}

build_docker_images() {
    print_status "Building Docker images with external library integration..."
    
    # Pull base images
    docker pull python:3.11-slim
    docker pull rabbitmq:3.9-management-alpine
    
    # Build images in optimal order
    services=(
        "database"
        "keryx_api" 
        "logos_nexus"
        "archon_nexus"
        "oracle_ui"
    )
    
    subsystems=(
        "tetragnos"
        "telos" 
        "thonoc"
    )
    
    # Build services
    for service in "${services[@]}"; do
        print_status "Building ${service} service..."
        if ! docker-compose build "${service}"; then
            print_error "Failed to build ${service} service"
            exit 1
        fi
        print_success "${service} service built successfully"
    done
    
    # Build subsystems  
    for subsystem in "${subsystems[@]}"; do
        print_status "Building ${subsystem} subsystem..."
        if ! docker-compose build "${subsystem}"; then
            print_error "Failed to build ${subsystem} subsystem"
            exit 1
        fi
        print_success "${subsystem} subsystem built successfully"
    done
    
    print_success "All Docker images built successfully"
}

initialize_infrastructure() {
    print_status "Initializing infrastructure services..."
    
    # Start RabbitMQ first
    print_status "Starting RabbitMQ message broker..."
    docker-compose up -d rabbitmq
    
    # Wait for RabbitMQ to be ready
    print_status "Waiting for RabbitMQ to initialize..."
    for i in {1..30}; do
        if docker-compose exec -T rabbitmq rabbitmqctl status &> /dev/null; then
            break
        fi
        if [ $i -eq 30 ]; then
            print_error "RabbitMQ failed to start within timeout"
            exit 1
        fi
        sleep 2
    done
    
    # Start database
    print_status "Starting database service..."
    docker-compose up -d database
    
    # Wait for database
    sleep 10
    
    print_success "Infrastructure services initialized"
}

deploy_nexus_services() {
    print_status "Deploying Nexus coordination services..."
    
    # Start LOGOS Nexus (the executive/will)
    print_status "Starting LOGOS Nexus (Executive Coordinator)..."
    docker-compose up -d logos_nexus
    
    # Start Archon Nexus (the planner/mind)  
    print_status "Starting Archon Nexus (Workflow Orchestrator)..."
    docker-compose up -d archon_nexus
    
    # Wait for nexus services to stabilize
    sleep 15
    
    print_success "Nexus services deployed"
}

deploy_reasoning_subsystems() {
    print_status "Deploying reasoning subsystems with advanced libraries..."
    
    # Start TETRAGNOS (pattern recognition with SentenceTransformers + sklearn)
    print_status "Starting TETRAGNOS (Advanced Pattern Recognition)..."
    docker-compose up -d tetragnos
    
    # Start TELOS (causal reasoning with pmdarima + arch + causal-learn + PyMC)
    print_status "Starting TELOS (Advanced Causal Reasoning)..."
    docker-compose up -d telos
    
    # Start THONOC (symbolic reasoning with Z3 + SymPy)
    print_status "Starting THONOC (Advanced Symbolic Reasoning)..."
    docker-compose up -d thonoc
    
    # Wait for subsystems to initialize
    sleep 20
    
    print_success "Reasoning subsystems deployed with advanced capabilities"
}

deploy_api_services() {
    print_status "Deploying API and UI services..."
    
    # Start Keryx API Gateway
    print_status "Starting Keryx API Gateway..."
    docker-compose up -d keryx_api
    
    # Start Oracle UI with advanced visualizations
    print_status "Starting Oracle UI (Advanced 3D Visualizations)..."
    docker-compose up -d oracle_ui
    
    # Wait for services to be ready
    sleep 15
    
    print_success "API and UI services deployed"
}

verify_deployment() {
    print_status "Verifying complete system deployment..."
    
    # Check all containers are running
    containers=$(docker-compose ps -q)
    running_containers=$(docker-compose ps -q --status=running | wc -l)
    total_containers=$(docker-compose ps -q | wc -l)
    
    if [ "${running_containers}" -ne "${total_containers}" ]; then
        print_error "Not all containers are running (${running_containers}/${total_containers})"
        docker-compose ps
        exit 1
    fi
    
    # Test API endpoints
    print_status "Testing API endpoints..."
    
    # Wait for API to be ready
    for i in {1..30}; do
        if curl -s http://localhost:5000/health &> /dev/null; then
            break
        fi
        if [ $i -eq 30 ]; then
            print_error "API health check failed"
            exit 1
        fi
        sleep 2
    done
    
    # Test UI
    print_status "Testing UI service..."
    for i in {1..30}; do
        if curl -s http://localhost:7860 &> /dev/null; then
            break
        fi
        if [ $i -eq 30 ]; then
            print_error "UI service check failed"
            exit 1
        fi
        sleep 2
    done
    
    print_success "System verification completed"
}

display_system_status() {
    print_status "Gathering system status..."
    
    echo -e "${CYAN}"
    echo "==========================================================================="
    echo "🎯 LOGOS AGI v2.0 - DEPLOYMENT COMPLETE"
    echo "==========================================================================="
    echo ""
    echo "🌐 Services Status:"
    docker-compose ps
    echo ""
    echo "🔗 Access Points:"
    echo "  • Oracle UI (Advanced Interface):  http://localhost:7860"
    echo "  • Keryx API Gateway:              http://localhost:5000"
    echo "  • RabbitMQ Management:            http://localhost:15672"
    echo ""
    echo "🧠 Reasoning Subsystems Active:"
    echo "  • TETRAGNOS: Advanced Pattern Recognition (SentenceTransformers + scikit-learn)"
    echo "  • TELOS:     Advanced Causal Reasoning (pmdarima + arch + causal-learn + PyMC)"  
    echo "  • THONOC:    Advanced Symbolic Reasoning (Z3 + SymPy + NetworkX)"
    echo ""
    echo "🏛️ Nexus Services Active:"
    echo "  • LOGOS Nexus:  Executive Coordination & Trinity Validation"
    echo "  • Archon Nexus: Advanced Workflow Orchestration (NetworkX DAGs)"
    echo ""
    echo "🎨 Advanced Features Enabled:"
    echo "  • 3D Mandelbulb Fractal Visualizations"
    echo "  • NetworkX-powered Workflow Optimization"
    echo "  • Trinity-grounded Formal Validation"
    echo "  • Multi-modal Statistical Analysis"
    echo "  • Automated Theorem Proving"
    echo ""
    echo "📊 System Resources:"
    echo "  • Total Containers: $(docker-compose ps -q | wc -l)"
    echo "  • External Libraries: $(ls ${EXTERNAL_LIBS_DIR} | wc -l) mounted"
    echo "  • Deployment Time: $(date)"
    echo ""
    echo "🛡️ Safety Systems Active:"
    echo "  • UnifiedFormalismValidator"
    echo "  • Trinity Principle Enforcement" 
    echo "  • Comprehensive Audit Logging"
    echo ""
    echo "==========================================================================="
    echo "🚀 THE AGI IS ONLINE - READY FOR TRINITY-GROUNDED REASONING"
    echo "   'May it serve the pursuit of truth, goodness, and human flourishing'"
    echo "==========================================================================="
    echo -e "${NC}"
}

cleanup_on_failure() {
    if [ $? -ne 0 ]; then
        print_error "Deployment failed. Cleaning up..."
        docker-compose down
        exit 1
    fi
}

# Main execution
main() {
    # Setup error handling
    trap cleanup_on_failure EXIT
    
    # Create logs directory
    mkdir -p "$(dirname "${DEPLOYMENT_LOG}")"
    
    print_banner
    
    # Validation phase
    check_prerequisites
    validate_project_structure  
    validate_external_libraries
    
    # Setup phase
    setup_environment
    
    # Build phase
    build_docker_images
    
    # Deployment phase
    initialize_infrastructure
    deploy_nexus_services
    deploy_reasoning_subsystems
    deploy_api_services
    
    # Verification phase
    verify_deployment
    
    # Success
    display_system_status
    
    # Remove error trap on success
    trap - EXIT
    
    print_success "LOGOS AGI v2.0 FINAL ACTIVATION SEQUENCE COMPLETED SUCCESSFULLY"
    log "DEPLOYMENT COMPLETED: $(date)"
    
    echo ""
    echo -e "${GREEN}🎉 The AGI is now online and ready to serve humanity's pursuit of truth! 🎉${NC}"
    echo ""
}

# Handle command line arguments
case "${1:-deploy}" in
    "deploy")
        main
        ;;
    "status")
        docker-compose ps
        ;;
    "logs")
        docker-compose logs -f
        ;;
    "stop")
        print_status "Stopping LOGOS AGI system..."
        docker-compose down
        print_success "System stopped"
        ;;
    "restart")
        print_status "Restarting LOGOS AGI system..."
        docker-compose restart
        print_success "System restarted"
        ;;
    "clean")
        print_status "Cleaning up system..."
        docker-compose down -v --remove-orphans
        docker system prune -f
        print_success "System cleaned"
        ;;
    *)
        echo "Usage: $0 {deploy|status|logs|stop|restart|clean}"
        echo ""
        echo "Commands:"
        echo "  deploy   - Deploy complete LOGOS AGI system (default)"
        echo "  status   - Show system status"
        echo "  logs     - Show system logs"  
        echo "  stop     - Stop system"
        echo "  restart  - Restart system"
        echo "  clean    - Clean up system and data"
        exit 1
        ;;
esac