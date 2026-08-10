with open("/workspace/leanproject/Submission/generate_final_v15.py", "r") as f:
    text = f.read()

# Make sure line 29 is exactly correct without double-prepending set_option
text = text.replace('header = "set_option maxHeartbeats 1000000\\n" + "".join(header_lines)', 'header = "".join(header_lines).replace("import FormalConjectures.Util.ProblemImports", "import FormalConjectures.Util.ProblemImports\\n\\nset_option maxHeartbeats 1000000")')

with open("/workspace/leanproject/Submission/generate_final_v15.py", "w") as f:
    f.write(text)

print("generate_final_v15.py updated successfully!")
