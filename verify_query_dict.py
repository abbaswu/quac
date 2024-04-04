import argparse
import json


def verify_query_dict(query_dict: object) -> None:
    assert isinstance(query_dict, dict)
    for module_name, module_name_level_query_dict in query_dict.items():
        assert isinstance(module_name, str)
        assert isinstance(module_name_level_query_dict, dict)
        for class_name_or_global, class_name_or_global_level_query_dict in module_name_level_query_dict.items():
            assert isinstance(class_name_or_global, str)
            assert isinstance(class_name_or_global_level_query_dict, dict)
            for function_name, parameter_name_or_return_level_query_dict in class_name_or_global_level_query_dict.items():
                assert isinstance(function_name, str)
                for parameter_name_or_return in parameter_name_or_return_level_query_dict:
                    assert isinstance(parameter_name_or_return, str)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-q', '--query-dict', type=str, required=True, help='Query dict JSON file, e.g. {"src.meerkat.configurations.infrastructure.rest.health.registry": {"HealthService": {"boot": ["container"]}}, "src.meerkat.data_providers.database.mongo.transformers": {"PostDocumentTransformer": {"transform_to_domain_object": ["return"]}}, "src.meerkat.domain.post.value_objects.id": {"Id": {"__init__": ["value"]}}, "src.meerkat.entrypoints.rest.post.registry": {"PostService": {"boot": ["container"]}}}')
    args = parser.parse_args()

    with open(args.query_dict, 'r') as fp:
        query_dict = json.load(fp)
        verify_query_dict(query_dict)
