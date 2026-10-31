.PHONY: setup verify check

export PYTHONDONTWRITEBYTECODE = 1

setup:
	lake update
	lake exe cache get

verify:
	python3 scripts/verify.py

check:
	python3 scripts/check_archive.py
