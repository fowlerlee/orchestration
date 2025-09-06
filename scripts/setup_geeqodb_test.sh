#!/bin/bash

# Test script for GeeqoDB setup
# This script tests the setup functionality

set -e

echo "Testing GeeqoDB setup script..."

# Test 1: Check if the setup script exists and is executable
if [ ! -f "scripts/setup_geeqodb.sh" ]; then
    echo "ERROR: setup_geeqodb.sh not found"
    exit 1
fi

if [ ! -x "scripts/setup_geeqodb.sh" ]; then
    echo "ERROR: setup_geeqodb.sh is not executable"
    exit 1
fi

echo "✓ Setup script exists and is executable"

# Test 2: Check if git is available
if ! command -v git &> /dev/null; then
    echo "ERROR: git is not installed"
    exit 1
fi

echo "✓ Git is available"

# Test 3: Check if zig is available
if ! command -v zig &> /dev/null; then
    echo "ERROR: zig is not installed"
    exit 1
fi

echo "✓ Zig is available"

# Test 4: Test dry run (check if script can parse arguments)
echo "Testing dry run..."
if ! bash -n scripts/setup_geeqodb.sh; then
    echo "ERROR: Setup script has syntax errors"
    exit 1
fi

echo "✓ Setup script syntax is valid"

echo "All tests passed!"
