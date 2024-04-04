import argparse
import json
import sys

from collections import defaultdict
from collections.abc import Iterable, Generator
from enum import Enum, auto

from query_result_dict import QueryDict, RawResultDefaultdict, RawResultDict, raw_result_dict_from_query_dict_and_raw_result_defaultdict


def filter_pyre_stdout(lines: Iterable[str]) -> Generator[str, None, None]:
    for line in lines:
        stripped_line = line.strip()
        # Skip blank lines
        if stripped_line:
            # Trim the 'ƛ ' at the beginning of some lines
            if stripped_line.startswith('ƛ '):
                yield stripped_line[2:]
            else:
                yield stripped_line


class State(Enum):
    BEFORE_RAW_INFER_OUTPUTS = auto()
    DURING_RAW_INFER_OUTPUTS = auto()
    AFTER_RAW_INFER_OUTPUTS = auto()


def extract_raw_infer_outputs_from_pyre_stdout(lines: Iterable[str]) -> dict:
    # state machine design pattern
    state: State = State.BEFORE_RAW_INFER_OUTPUTS

    lines_in_json: list[str] = []

    for filtered_line in filter_pyre_stdout(lines):
        if state == State.BEFORE_RAW_INFER_OUTPUTS:
            if filtered_line == 'Raw Infer Outputs:':
                state = State.DURING_RAW_INFER_OUTPUTS
            else:
                state = State.BEFORE_RAW_INFER_OUTPUTS
        elif state == State.DURING_RAW_INFER_OUTPUTS:
            if filtered_line == 'Generated Stubs:':
                state = State.AFTER_RAW_INFER_OUTPUTS
            else:
                lines_in_json.append(filtered_line)
                state = State.DURING_RAW_INFER_OUTPUTS
        elif state == State.AFTER_RAW_INFER_OUTPUTS:
            state = State.AFTER_RAW_INFER_OUTPUTS

    return json.loads('\n'.join(lines_in_json))


def get_relevant_define_dicts(
    query_dict: QueryDict,
    raw_infer_outputs: dict
) -> Generator[dict, None, None]:
    for define_dict in raw_infer_outputs['defines']:
        # module_name: 'tests.meerkat.domain.post.use_cases.test_publish_post'
        module_name: str = define_dict['location']['qualifier']

        if module_name in query_dict:
            yield define_dict


def parse(
    query_dict: QueryDict,
    lines: Iterable[str]
) -> RawResultDict:
    raw_infer_outputs: dict = extract_raw_infer_outputs_from_pyre_stdout(lines)

    raw_result_defaultdict: RawResultDefaultdict = defaultdict(lambda: defaultdict(lambda: defaultdict(lambda: defaultdict(list))))

    # relevant_define_dict: {'name': 'src.meerkat.configurations.infrastructure.rest.health.registry.HealthService.boot', 'location': {'qualifier': 'src.meerkat.configurations.infrastructure.rest.health.registry', 'path': '/tmp/module_search_path/src/meerkat/configurations/infrastructure/rest/health/registry.py', 'line': 8}, 'parent': 'src.meerkat.configurations.infrastructure.rest.health.registry.HealthService', 'return': 'None', 'parameters': [{'name': 'self', 'index': 0, 'annotation': None, 'value': None}, {'name': 'container', 'index': 1, 'annotation': None, 'value': None}], 'async': False}
    for relevant_define_dict in get_relevant_define_dicts(query_dict, raw_infer_outputs):
        # name: 'src.meerkat.configurations.infrastructure.rest.health.registry.HealthService.boot'
        name: str = relevant_define_dict['name']

        # module_name: 'src.meerkat.configurations.infrastructure.rest.health.registry'
        module_name: str = relevant_define_dict['location']['qualifier']

        # parent: 'src.meerkat.configurations.infrastructure.rest.health.registry.HealthService'
        parent: str | None = relevant_define_dict['parent']

        if parent is not None:
            # class_name_or_global: 'HealthService'
            class_name_or_global: str = parent[len(module_name) + 1:]

            # function_name: 'boot'
            function_name: str = name[len(parent) + 1:]
        else:
            class_name_or_global: str = 'global'
            function_name: str = name[len(module_name) + 1:]
        
        # parameter_dict: {'name': 'self', 'index': 0, 'annotation': None, 'value': None}
        for parameter_dict in relevant_define_dict['parameters']:
            # parameter_name: 'self'
            parameter_name: str = parameter_dict['name']

            parameter_annotation_string_or_none: str | None = parameter_dict['annotation']
            if parameter_annotation_string_or_none is not None:
                raw_result_defaultdict[module_name][class_name_or_global][function_name][parameter_name].append(parameter_annotation_string_or_none)

        return_annotation_string_or_none: str | None = relevant_define_dict['return']
        if return_annotation_string_or_none is not None:
            raw_result_defaultdict[module_name][class_name_or_global][function_name]['return'].append(return_annotation_string_or_none)
    
    return raw_result_dict_from_query_dict_and_raw_result_defaultdict(
        query_dict,
        raw_result_defaultdict
    )


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-q', '--query-dict', type=str, required=True, help='Query dict JSON file, e.g. {"src.meerkat.configurations.infrastructure.rest.health.registry": {"HealthService": {"boot": ["container"]}}, "src.meerkat.data_providers.database.mongo.transformers": {"PostDocumentTransformer": {"transform_to_domain_object": ["return"]}}, "src.meerkat.domain.post.value_objects.id": {"Id": {"__init__": ["value"]}}, "src.meerkat.entrypoints.rest.post.registry": {"PostService": {"boot": ["container"]}}}')
    args = parser.parse_args()

    with open(args.query_dict, 'r') as fp:
        query_dict = json.load(fp)

    result_dict = parse(query_dict, sys.stdin)
    
    json.dump(result_dict, sys.stdout)
