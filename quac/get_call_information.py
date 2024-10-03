import ast


def get_call_information(
    call_node: ast.Call
):
    # ast.Call(func, args, keywords, starargs, kwargs)
    func = call_node.func

    contains_starred_arguments_or_keywords = False

    non_starred_arguments = []
    for arg in call_node.args:
        if not isinstance(arg, ast.Starred):
            non_starred_arguments.append(arg)
        else:
            contains_starred_arguments_or_keywords = True
            break

    keyword_args_to_values = {}
    for keyword in call_node.keywords:
        if keyword.arg is not None:
            keyword_args_to_values[keyword.arg] = keyword.value

    if call_node.keywords:
        contains_starred_arguments_or_keywords = True

    return func, non_starred_arguments, keyword_args_to_values, contains_starred_arguments_or_keywords

