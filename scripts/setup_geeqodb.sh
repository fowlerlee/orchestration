#!/bin/bash

# GeeqoDB Setup Script
# This script downloads and builds GeeqoDB for the orchestration project

set -e  # Exit on any error

# Configuration
REPO_URL="git@github.com:fowlerlee/geeqodb.git"
REPO_NAME="geeqodb"
DATABASE_DIR="database"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_status() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Function to show usage
show_usage() {
    echo "GeeqoDB Setup Script"
    echo ""
    echo "Usage: $0 [OPTIONS]"
    echo ""
    echo "Options:"
    echo "  -h, --help          Show this help message"
    echo "  -d, --download-only Only download the repository, don't build"
    echo "  -b, --build-only    Only build (assumes repository already exists)"
    echo "  -c, --clean         Clean up existing repository and database directory"
    echo "  -v, --verbose       Enable verbose output"
    echo ""
    echo "Examples:"
    echo "  $0                  # Download and build GeeqoDB"
    echo "  $0 --download-only  # Only download the repository"
    echo "  $0 --build-only     # Only build (repository must exist)"
    echo "  $0 --clean          # Clean and rebuild everything"
}

# Parse command line arguments
DOWNLOAD_ONLY=false
BUILD_ONLY=false
CLEAN=false
VERBOSE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_usage
            exit 0
            ;;
        -d|--download-only)
            DOWNLOAD_ONLY=true
            shift
            ;;
        -b|--build-only)
            BUILD_ONLY=true
            shift
            ;;
        -c|--clean)
            CLEAN=true
            shift
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        *)
            print_error "Unknown option: $1"
            show_usage
            exit 1
            ;;
    esac
done

# Function to check prerequisites
check_prerequisites() {
    print_status "Checking prerequisites..."
    
    # Check if git is available
    if ! command -v git &> /dev/null; then
        print_error "git is not installed or not in PATH"
        print_error "Please install git first: https://git-scm.com/downloads"
        exit 1
    fi
    
    # Check if zig is available
    if ! command -v zig &> /dev/null; then
        print_error "zig is not installed or not in PATH"
        print_error "Please install zig first: https://ziglang.org/download/"
        exit 1
    fi
    
    # Check git version
    GIT_VERSION=$(git --version | cut -d' ' -f3)
    print_success "Git version: $GIT_VERSION"
    
    # Check zig version
    ZIG_VERSION=$(zig version)
    print_success "Zig version: $ZIG_VERSION"
    
    print_success "Prerequisites check passed"
}

# Function to clean up existing files
cleanup() {
    print_status "Cleaning up existing files..."
    
    cd "$PROJECT_ROOT"
    
    if [ -d "$REPO_NAME" ]; then
        print_status "Removing existing $REPO_NAME directory..."
        rm -rf "$REPO_NAME"
        print_success "Removed $REPO_NAME directory"
    fi
    
    if [ -d "$DATABASE_DIR" ]; then
        print_status "Removing existing $DATABASE_DIR directory..."
        rm -rf "$DATABASE_DIR"
        print_success "Removed $DATABASE_DIR directory"
    fi
}

# Function to download the repository
download_repository() {
    print_status "Downloading GeeqoDB repository..."
    
    cd "$PROJECT_ROOT"
    
    # Check if repository already exists
    if [ -d "$REPO_NAME" ]; then
        if [ "$CLEAN" = false ]; then
            print_warning "Repository $REPO_NAME already exists"
            read -p "Do you want to update it? (y/N): " -n 1 -r
            echo
            if [[ $REPLY =~ ^[Yy]$ ]]; then
                print_status "Updating existing repository..."
                cd "$REPO_NAME"
                git pull origin main
                cd "$PROJECT_ROOT"
                print_success "Repository updated"
            else
                print_status "Using existing repository"
                return 0
            fi
        else
            print_status "Removing existing repository for clean build..."
            rm -rf "$REPO_NAME"
        fi
    fi
    
    # Clone the repository
    print_status "Cloning repository from $REPO_URL..."
    if [ "$VERBOSE" = true ]; then
        git clone "$REPO_URL" "$REPO_NAME"
    else
        git clone "$REPO_URL" "$REPO_NAME" 2>/dev/null
    fi
    
    if [ $? -eq 0 ]; then
        print_success "Repository cloned successfully"
    else
        print_error "Failed to clone repository"
        print_error "Make sure you have access to the repository and SSH keys are set up"
        exit 1
    fi
}

# Function to build the database
build_database() {
    print_status "Building GeeqoDB..."
    
    cd "$PROJECT_ROOT/$REPO_NAME"
    
    # Check if build.zig exists
    if [ ! -f "build.zig" ]; then
        print_error "build.zig not found in repository"
        print_error "Make sure the repository contains a valid Zig project"
        exit 1
    fi
    
    # Build the project
    print_status "Running 'zig build'..."
    if [ "$VERBOSE" = true ]; then
        zig build
    else
        zig build 2>/dev/null
    fi
    
    if [ $? -eq 0 ]; then
        print_success "GeeqoDB built successfully"
    else
        print_error "Failed to build GeeqoDB"
        print_error "Check the build output above for errors"
        exit 1
    fi
    
    # Find and copy the binary
    copy_binary
}

# Function to copy the built binary
copy_binary() {
    print_status "Copying GeeqoDB binary..."
    
    cd "$PROJECT_ROOT"
    
    # Create database directory
    mkdir -p "$DATABASE_DIR"
    
    # Find the built binary
    BINARY_FOUND=false
    
    # Check common binary locations
    POSSIBLE_PATHS=(
        "$REPO_NAME/zig-out/bin/geeqodb"
        "$REPO_NAME/geeqodb"
        "$REPO_NAME/zig-out/bin/geeqodb.exe"
        "$REPO_NAME/geeqodb.exe"
    )
    
    for path in "${POSSIBLE_PATHS[@]}"; do
        if [ -f "$path" ]; then
            print_status "Found binary at: $path"
            cp "$path" "$DATABASE_DIR/"
            chmod +x "$DATABASE_DIR/$(basename "$path")"
            print_success "Binary copied to $DATABASE_DIR/"
            BINARY_FOUND=true
            break
        fi
    done
    
    if [ "$BINARY_FOUND" = false ]; then
        print_warning "Could not find built binary in expected locations"
        print_warning "Please check the build output and manually copy the binary to $DATABASE_DIR/"
    fi
}

# Function to create configuration
create_config() {
    print_status "Creating GeeqoDB configuration..."
    
    cd "$PROJECT_ROOT"
    
    # Create config.toml
    cat > "$DATABASE_DIR/config.toml" << EOF
# GeeqoDB Configuration
[server]
host = "0.0.0.0"
port = 8080
max_connections = 100

[storage]
data_dir = "./data"
wal_dir = "./wal"
max_file_size = "1GB"

[replication]
enabled = true
replica_count = 3
EOF
    
    # Create data directories
    mkdir -p "$DATABASE_DIR/data"
    mkdir -p "$DATABASE_DIR/wal"
    
    print_success "Configuration created at $DATABASE_DIR/config.toml"
}

# Function to show completion message
show_completion() {
    print_success "GeeqoDB setup completed successfully!"
    echo ""
    echo "Next steps:"
    echo "1. Start the database server:"
    echo "   cd $DATABASE_DIR && ./geeqodb --config config.toml"
    echo ""
    echo "2. Or use the worker integration:"
    echo "   go run cmd/main.go"
    echo ""
    echo "Files created:"
    echo "  - $DATABASE_DIR/geeqodb (binary)"
    echo "  - $DATABASE_DIR/config.toml (configuration)"
    echo "  - $DATABASE_DIR/data/ (data directory)"
    echo "  - $DATABASE_DIR/wal/ (WAL directory)"
}

# Main execution
main() {
    print_status "Starting GeeqoDB setup..."
    print_status "Project root: $PROJECT_ROOT"
    
    # Check prerequisites
    check_prerequisites
    
    # Clean if requested
    if [ "$CLEAN" = true ]; then
        cleanup
    fi
    
    # Download repository (unless build-only)
    if [ "$BUILD_ONLY" = false ]; then
        download_repository
    fi
    
    # Build database (unless download-only)
    if [ "$DOWNLOAD_ONLY" = false ]; then
        build_database
        create_config
        show_completion
    else
        print_success "Download completed. Run with --build-only to build."
    fi
}

# Run main function
main "$@"
