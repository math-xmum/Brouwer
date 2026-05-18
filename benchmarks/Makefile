PYTHON ?= python3
MODEL ?= qwen3:8b
DATASET ?= data/brouwerbench_v0.jsonl
SAFE_MODEL := $(subst :,_,$(subst /,_,$(MODEL)))
RESULT := results/brouwerbench_v0__$(SAFE_MODEL).jsonl
SCORES := scores/brouwerbench_v0__$(SAFE_MODEL).manual.jsonl

.PHONY: qwen3 run score validate

qwen3: run score

run:
	$(PYTHON) scripts/run_ollama_benchmark.py \
		--model $(MODEL) \
		--dataset $(DATASET) \
		--output $(RESULT) \
		--overwrite

score:
	$(PYTHON) scripts/score_benchmark.py \
		--dataset $(DATASET) \
		--results $(RESULT) \
		--scores $(SCORES)

validate:
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -m py_compile \
		scripts/run_ollama_benchmark.py \
		scripts/score_benchmark.py
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -c "import json, pathlib; [json.loads(line) for line in pathlib.Path('$(DATASET)').read_text().splitlines() if line.strip()]; print('dataset ok')"
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -c "import pathlib; sections={'Scarf','Brouwer','Brouwer_product','Nash'}; missing=[s for s in sections if not pathlib.Path(f'context/{s}.lean-snippet').exists()]; assert not missing, missing; print('context snippets ok')"
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -c "import json, pathlib; root=pathlib.Path('.').resolve().parent; rows=[json.loads(line) for line in pathlib.Path('$(DATASET)').read_text().splitlines() if line.strip()]; missing=[r['id'] for r in rows if not (root / r['section_prelude']).exists()]; assert not missing, missing; print('dataset prelude links ok')"
