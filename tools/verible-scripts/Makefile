all: venv env

# Check for RV_ROOT
ifeq (,$(wildcard ${RV_ROOT}/configs/veer.config))
$(error env var RV_ROOT does not point to a valid dir! Exiting!)
endif

venv:
	@echo "# Build virtual environment in venv/bin/python"
	python3 -m venv venv

env:
	@echo "# Activate venv in a new shell"
	@env bash --init-file "$(PWD)/venv/bin/activate"

