#!/usr/bin/env bash
source .venv/bin/activate

TIMEFORMAT="%R"

rm -rf .mypy_cache
real_time=$( { time mypy benchmarks/rl_models/agents.py >/dev/null 2>&1; } 2>&1 )

for i in {1..10}; do
    real_time=$( { time mypy benchmarks/rl_models/agents.py >/dev/null 2>&1; } 2>&1 )
    echo "$real_time"
done
