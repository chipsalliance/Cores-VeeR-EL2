# Methods shared by tests

import json

import validate_metrics as vm

# Repository of run_metadata(), the tests' configs use it to accept the runs
REPOSITORY = "org/repo"

# Validators of the real schemas, by schema name
VALIDATORS = {
    name: vm.load_schema(vm.SCHEMA_DIR / f"{name}.schema.json")
    for name in ("metrics", "metadata", "config", "unit_types")
}


def write_json(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content if isinstance(content, str) else json.dumps(content))
    return path


def run_metadata(*, pr=None, branch="main", repository=REPOSITORY):
    metadata = {
        "date": "2026-11-05 12:58",
        "current_commit": "0ad8541c1",
        "is_pr": pr is not None,
        "source_branch": branch,
        "source_repository": repository,
    }
    if pr is not None:
        metadata.update(pr_number=pr, pr_title=f"PR {pr}", target_repository=repository)
    return metadata


def write_run(directory, name, metrics, metadata):
    """'<name>.json' and, unless metadata is None, '<name>.metadata.json'."""
    path = write_json(directory / f"{name}.json", metrics)
    if metadata is not None:
        write_json(directory / f"{name}.metadata.json", metadata)
    return path


def write_config(directory, config, unit_types):
    """Config file, with its unit types file next to it."""
    write_json(directory / config["unit_types_file"], unit_types)
    return write_json(directory / "config.json", config)
