def parse_plaintext_layout(plaintext_str):
    """Parse plaintext_str in Plaintext format into ndarray layout

    typical plaintext_str format:
    '''
    .O.O
    O.O
    O
    ......O
    '''


    """
    # if isinstance(plaintext_str, list):
    #     # already line-split
    #     lines = plaintext_str
    # else:
    # split lines, ignore comments
    lines = plaintext_str.strip().replace("\r\n", "\n").split("\n")
    lines = [line for line in lines if not line.startswith("!")]

    # check if only '.' and 'O' are present
    if set("".join(lines)) != {".", "O"}:
        raise ValueError("Invalid input cells_str : use only '.' and 'O'")

    layout = [[1 if c == "O" else 0 for c in line] for line in lines]

    max_width = max(len(line) for line in layout)

    return max_width