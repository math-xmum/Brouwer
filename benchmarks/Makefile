PYTHON ?= python3
MODEL ?= qwen3:8b
DATASET ?= data/brouwerbench_v1.jsonl
DATASET_STEM := $(basename $(notdir $(DATASET)))
SAFE_MODEL := $(subst :,_,$(subst /,_,$(MODEL)))
RESULT := results/$(DATASET_STEM)__$(SAFE_MODEL).jsonl
SCORES := scores/$(DATASET_STEM)__$(SAFE_MODEL).manual.jsonl

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
		scripts/score_benchmark.py \
		scripts/validate_dataset.py
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) scripts/validate_dataset.py --dataset $(DATASET)
