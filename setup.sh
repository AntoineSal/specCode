#!/usr/bin/env bash
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "==> Installing speccode package..."
pip install -e .

echo ""
echo "==> Setting up .env..."
if [ ! -f .env ]; then
    cp .env.example .env
    echo "    Created .env from .env.example — please fill in your MISTRAL_API_KEY."
else
    echo "    .env already exists, skipping."
fi

echo ""
echo "==> Updating Lean project dependencies..."
cd lean_project
lake update

echo ""
echo "==> Downloading Mathlib precompiled cache..."
lake exe cache get

echo ""
echo "==> Done!"
echo "    Edit .env to add your MISTRAL_API_KEY, then run: speccode"
