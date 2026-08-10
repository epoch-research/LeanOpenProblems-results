import math

def generate():
    # 1.2 million elements, each 4 characters
    size = 1200000
    print(f"Generating string of size {size * 4} characters...")
    chars = []
    for i in range(size):
        chars.append(f"{i % 65536:04x}")
    large_str = "".join(chars)
    
    code = f"""import FormalConjectures.Util.ProblemImports

def large_string : String := "{large_str}"
def large_bytes : ByteArray := large_string.toUTF8

#eval large_bytes.size
"""
    with open("/workspace/leanproject/Submission/TestLargeString.lean", "w") as f:
        f.write(code)
    print("Done generating TestLargeString.lean")

if __name__ == "__main__":
    generate()
