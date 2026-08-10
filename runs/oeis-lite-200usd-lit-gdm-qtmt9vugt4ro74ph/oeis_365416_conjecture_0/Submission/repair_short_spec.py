def main():
    with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
        lines = f.readlines()

    new_lines = []
    for line in lines:
        if '\\n    out.append("""' in line or ')\\\\n    out.append("""' in line or ')\\n    out.append("""' in line:
            # Split the line by the bad newline escape
            parts = line.split('out.append("""')
            new_lines.append('    out.append(test_content)\n')
            new_lines.append('    out.append("""' + parts[1])
        else:
            new_lines.append(line)

    with open("/workspace/leanproject/Submission/generate_short_spec.py", "w") as f:
        f.writelines(new_lines)

if __name__ == "__main__":
    main()
