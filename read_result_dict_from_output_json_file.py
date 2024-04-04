import json
import logging

from parse_type_inference_result import parse


def read_result_dict_from_output_json_file(output_json_file_path):
    with open(output_json_file_path, 'r') as fp:
        output = json.load(fp)

    for m, md in output.items():
        for c, cd in md.items():
            for f, fd in cd.items():
                for p in fd:
                    ts = fd[p]

                    parsed = []
                    for t in ts:
                        try:
                            parsed.append(parse(t))
                        except:
                            logging.exception('Failed to parse type annotation %s', t)

                    fd[p] = parsed

    return output

