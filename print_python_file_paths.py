import argparse
import json

from python_file_path_from_module_search_path_and_module_name import python_file_path_from_module_search_path_and_module_name


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-q', '--query-dict', type=str, required=True, help='Query dict JSON file, e.g. {"src.meerkat.configurations.infrastructure.rest.health.registry": {"HealthService": {"boot": ["container"]}}, "src.meerkat.data_providers.database.mongo.transformers": {"PostDocumentTransformer": {"transform_to_domain_object": ["return"]}}, "src.meerkat.domain.post.value_objects.id": {"Id": {"__init__": ["value"]}}, "src.meerkat.entrypoints.rest.post.registry": {"PostService": {"boot": ["container"]}}}')
    parser.add_argument('-s', '--module-search-path', type=str, required=True, help='Module search path, e.g. /tmp/module_search_path')
    args = parser.parse_args()

    with open(args.query_dict, 'r') as fp:
        query_dict = json.load(fp)

    module_search_path = args.module_search_path

    for module_name in query_dict:
        print(
            python_file_path_from_module_search_path_and_module_name(
                module_search_path,
                module_name
            )
        )
