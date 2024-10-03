# QuAC: Quick Attribute-Centric Type Inference for Python

All source code for the QuAC tool proposed in the OOPSLA 2024 paper "QuAC: Quick Attribute-Centric Type Inference for Python." **NOTE: This only includes QuAC's implementation, and not the benchmarks, baselines, and data analysis code. To reproduce the results in the paper, please download the reproduction package at https://doi.org/10.5281/zenodo.13367665**

## Requirements and Assumptions

- **IMPORTANT: QuAC attempts to dynamically import the Python files under your Python project as modules! Make sure this is possible, and doing this has no nasty side effects (e.g., by wrapping Python files intended to be directly executed instead of imported under a `if __name__ == '__main__'` block)!**
- You have a Python **virtual environment** with **Python 3.10 or above**.
- Your Python project under analysis has all modules written in **pure Python** (no Cython/C code, no FFIs).
- You should know the **absolute path of the directory containing Python modules---from that path, the Python interpreter must be able to import every module within the Python project successfully.** This depends from project to project. For example:
    - If you have cloned the [NetworkX](https://github.com/networkx/networkx.git) repository to `/tmp/networkx`, that directory should be `/tmp/networkx`.
    - If you have cloned the [typing_extensions](https://github.com/python/typing_extensions) repository to `/tmp/typing_extensions`, that directory should be `/tmp/typing_extensions/`
- Your Python project under analysis should either **have no dependencies** or **have all dependencies already installed under the Python environment QuAC is run**.

## Instructions

**Again, note that QuAC attempts to dynamically import the Python files under your Python project as modules! Make sure this is possible, and doing this has no nasty side effects (e.g., by wrapping Python files intended to be directly executed instead of imported under a `if __name__ == '__main__'` block)!**

- Set up a **Python 3.10 or above virtual environment** to run QuAC.
- Install QuAC's dependencies, listed in `requirements.txt`, **and any dependencies of your Python project under analysis**.
- Run `quac/main.py`:
  - Provide the **absolute path of the directory containing Python modules**.
  - Provide a **module prefix**. This filters out irrelevant modules that shouldn't be analyzed, such as installation files, example files, or test files. For example, given the [NetworkX](https://github.com/networkx/networkx.git) repository, providing the module prefix `networkx` allows us to analyze files such as `networkx/algorithms/clique.py` while skipping files such as `examples/external/plot_igraph.py`.
  - Provide an output JSON file.


For example, to run QuAC on the `bm_math` module in the `example/` directory and save output to `quac_output.json`:

```bash
python \
quac/main.py \
--module-search-path example/ \
--module-prefix 'bm_math' \
--output-file quac_output.json
```

The generated `quac_output.json` should resemble the following:

```json
{
    "bm_math": {
        "global": {
            "maximize": {
                "points": [
                    "typing.Sequence[bm_math.Point]"
                ],
                "return": [
                    "bm_math.Point"
                ]
            }
        },
        "Point": {
            "__init__": {
                "i": [],
                "return": []
            },
            "__repr__": {
                "return": [
                    "builtins.str"
                ]
            },
            "normalize": {
                "return": []
            },
            "maximize": {
                "other": [
                    "bm_math.Point"
                ],
                "return": [
                    "bm_math.Point"
                ]
            }
        }
    }
}
```

The JSON is organized into four levels:

- Top-Level Module Names
    - Global Function Names
        - Parameter Names or "return"
            - Type Predictions
    - Class Names
        - Method Names
            - Parameter Names or "return"
                - Type Predictions
