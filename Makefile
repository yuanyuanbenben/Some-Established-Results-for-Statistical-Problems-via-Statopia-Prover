.PHONY: setup verify replay check

export PYTHONDONTWRITEBYTECODE = 1

setup:
	lake update
	lake exe cache get

verify:
	python3 scripts/verify_minimal.py

replay:
	python3 scripts/replay_cache.py

check:
	python3 scripts/check_archive.py
