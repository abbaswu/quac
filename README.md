# QuAC: Quick Attribute-Centric Type Inference for Python

All source code for "QuAC: Quick Attribute-Centric Type Inference for Python." **NOTE: We plan to upload the benchmarks and data replication scripts by the artifact submission deadline of Fri 5 Jul 2024.**

This codebase is in the form of a *Docker container* containing the implementation of our type inference method QuAC (in the subdirectory `quac/`), the baseline type inference methods [Stray](https://github.com/ksun212/Stray) and [HiTyper](https://github.com/JohnnyPeng18/HiTyper) (code unmodified), and a pipeline to run a type inference method on a benchmark, post-process the results, and run `mypy` to check each type prediction.

## Requirements and Assumptions

- You are on a Unix-like system running on an x86-64 machine with Docker installed.
- Your Python project under analysis has all modules written in **pure Python** (no Cython/C code, no FFIs).
- You should know the **absolute path of the directory containing Python modules---from that path, the Python interpreter must be able to import every module within the Python project successfully.** This depends from project to project. For example:
    - If you have cloned the [NetworkX](https://github.com/networkx/networkx.git) repository to `/tmp/networkx`, that directory should be `/tmp/networkx`.
    - If you have cloned the [typing_extensions](https://github.com/python/typing_extensions) repository to `/tmp/typing_extensions`, that directory should be `/tmp/typing_extensions/`
- Your Python project under analysis should either **have no dependencies** or **have all dependencies explicitly listed in a `requirements.txt` file under the `absolute path of the directory containing Python modules`**.

## Instructions

Build the container from the GitHub repository.

```bash
docker build --tag quac .
```

Start Type4Py server (required for the baseline type inference method [HiTyper](https://github.com/JohnnyPeng18/HiTyper)).

```bash
docker pull ghcr.io/saltudelft/type4py:latest
docker run -d -p 5001:5010 -it ghcr.io/saltudelft/type4py:latest
```

Use the Docker container to run a type inference method on a Python project.

- Provide the **absolute path of the directory containing Python modules**.
- Provide the **absolute path of the output directory**. The following intermediate and final results will be saved in the output directory:
    - A JSON file `output.json` storing the (post-processed) results of running the type inference method.
    - A JSON file `time_output.json` storing the run time of the type inference method.
    - A CSV file `use_mypy_to_check_each_type_prediction.csv` storing `mypy`'s error messages from type-checking each type prediction.
    - A subdirectory `repository_for_type_checking/` storing a copy of the directory containing Python modules used for type-checking each type prediction. The line numbers in `use_mypy_to_check_each_type_prediction.csv` correspond to line numbers within the Python modules here.
    - A subdirectory `raw_output_directory/` storing the raw output of the type inference method.
- Provide a **type inference method**. Valid type inference methods are `'quac'`, `'stray'`, `'hityper'`.
- Provide a **module prefix**. This filters out irrelevant modules that shouldn't be analyzed, such as installation files, example files, or test files. For example, given the [NetworkX](https://github.com/networkx/networkx.git) repository, providing the module prefix `networkx` allows us to analyze files such as `networkx/algorithms/clique.py` while skipping files such as `examples/external/plot_igraph.py`.

```bash
docker run \
--rm \
--net=host \
-v <absolute path of the directory containing Python modules>:/mnt/mounted_module_search_path:ro \
-v <absolute path of the output directory>:/mnt/output_path \
quac \
-m <type inference method> \
-p <module prefix>
```

For example, to run QuAC on Python modules starting with `shell_sort` in the directory `/tmp/module_search_path` and save output to `/tmp/quac_output`:

```bash
docker run \
--rm \
--net=host \
-v /tmp/module_search_path:/mnt/mounted_module_search_path:ro \
-v /tmp/quac_output:/mnt/output_path \
quac \
-m quac \
-p shell_sort
```

## Code Organization

- `Dockerfile`: Self-explanatory.
- `Miniconda3-latest-Linux-x86_64.sh`: Used for installing a Conda environment within the Docker container.
- `quac`: Source code of QuAC.
- `stray/`, `hityper/`: Source code of the baseline type inference methods [Stray](https://github.com/ksun212/Stray) and [HiTyper](https://github.com/JohnnyPeng18/HiTyper).
- `container_entrypoint_shell_script.sh`: Entry point Shell script of the Docker container.
