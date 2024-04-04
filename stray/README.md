



## STRAY: a Static Type Recommendation Approach for pYthon

This is the prototype package for a ASE '22 paper "Static Type Recommendation for Python". 
The material mentioned in the paper (i.e., the extended Algorithm 1 and the proof of Theorem 2.1) are in the **Appendix** folder. 
The statistics mentioned in the paper (i.e., the statistics about the evaluation dataset and the time costing of different units) are in the **Additional Statistics** folder. 




### Installation
First, create and activate a Python environment, e.g.: 

```
conda create -n stray_exp python=3.9
conda activate stray_exp
```

Then, install the packages to run stray:

```
pip install -r requirements.txt
```

Note that two kinds of packages are installed: (1) the packages necessary to run stray, (2) the packages that are depended by our evaluation projects, i.e., the packages necessary to reproduce our experiments. 

### Reproduction

#### Handling Dependency
To precisely reproduce the results reported in the paper, you need to substitute several type stub files of numpy and matplotlib in their installation site with our version provided under data/pyi folder. 

Specifically, if you follow our instruction to install (using conda), you can 
```
cp -a data/pyi/numpy/. PATH_TO_CONDA/envs/stray_exp/lib/python3.9/site-packages/numpy
cp -a data/pyi/matplotlib-stubs/. PATH_TO_CONDA/envs/stray_exp/lib/python3.9/site-packages/matplotlib-stubs

```

The reason is that, by the time of our experiment, numpy had just started their annotation, some stub files are not complete, we provide necessary completion to them.  On the other hand, matplotlib has never introduced their offical annotation. Thus, the stubs are unofficial and thus, incomplete. We also provide necessary completion to them. 

#### Reproduction Scripts

We provide scripts to convinently reproduce the results reported in the paper, i.e., Table 1 & 2. 

```
python -m run_unittest_on_metric check
python -m run_unittest_on_metric predict
python -m evaluation.evaluate parameter
python -m evaluation.evaluate return
```
Note that we run run_unittests_on_metric twice. The first run is to simply check and generate type cache for third-party dependencies. The second run is to predict (recommend) types for benchmark projects. 

Also note that we run evaluation.evaluate twice. The first run is to evaluate the results on parameters, while the second run is to evaluate the results on returns. 

After the evaluation, find Table 1 in the table_parameter.txt, Table 2 in table_return.txt  

### Usage

To run stray for a single project, make sure that all its dependencies have been installed, for instance, for a project depending on A:

```
pip install A
```

then use the predict.py as the main entry.

For instance: 

```
python -m predict data/benchmark/tinychain check tinychain
python -m predict data/benchmark/tinychain predict tinychain
```

The first parameter is the project root; the second parameter is the executation mode (see the explanation in the last section); the third parameter is the name of the project. 

After the execution, find the results on the *results* folder. results/funcs-name is the index of each function, results/funcs_res-name is the recommended types for the corresponding function. For example: 
Suppose we have results/funcs-name as 
```
3    ...
4    tinychain.Transaction.validate_basics
5
6    tinychain.Block.header
7    ....
```
and results/funcs_res-name as 
```
3    builtins.str
4    None
5    builtins.object/builtins.int/builtins.float
6    builtins.str
7    builtins.int
```
Then the types for tinychain.Transaction.validate_basics is in the fourth and fifth line of results/funcs_res-name, i.e., the return type is None and the parameter type is builtins.object/builtins.int/builtins.float. 


### Structure

This project is based on the code of mypy 0.92 (https://github.com/python/mypy). On the basis of mypy, we write an abstract interpretation (a bottom-up traversal of the AST) added front-end interfaces to the abstract interpretation. All source codes are in the extyper folder. 

* The entry and the collection of tentative type seeds is the *process_project* function in *build.py*. 
* The abstract interpretation are *inferencer.py* and *inferexpr.py*


Also note that the constraints used in this implementation is reverse of the specification of the paper. That is, instead of collecting constraints that make type checks, we collect constraints that make type not checks. Since the two are dual, it should be easy to alter between them. 


