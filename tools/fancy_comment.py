import sys

def fancify(s : str):
    s = s.strip()
    n1 = (79 - len(s)) // 2
    n2 = (79 - len(s)) - n1
    return "%" + n1 * "=" + s.upper() + n2 * "="

if __name__ == "__main__":
    for s in sys.argv[1:]:
        print(fancify(s))
