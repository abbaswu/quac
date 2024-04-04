#!/bin/bash

set -e
set -o pipefail
set -x

rm .coverage
rm -R htmlcov/

coverage run --source=test_disjoint_set test_disjoint_set.py
coverage html

coverage run --source=scoped_evaluation_order_node_visitor test_scoped_evaluation_order_node_visitor.py
coverage html

coverage run --source=typeshed_client_ex,extract_single_non_none_typeshed_class test_typeshed_client_ex.py
coverage html

coverage run --source=get_definitions_to_runtime_terms_mappings test_get_definitions_to_runtime_terms_mappings.py
coverage html

coverage run --source=get_attribute_access_result test_get_attribute_access_result.py
coverage html

coverage run --source=handle_function_call test_handle_function_call.py
coverage html

coverage run --source=get_use_define_mapping test_get_use_define_mapping.py
coverage html

coverage run --source=get_module_names_to_imported_names_to_runtime_objects test_get_module_names_to_imported_names_to_runtime_objects.py
coverage html

coverage run --source=get_call_information test_get_call_information.py
coverage html

coverage run --source=iterate_inheritance_graph_layers test_iterate_inheritance_graph_layers.py
coverage html
