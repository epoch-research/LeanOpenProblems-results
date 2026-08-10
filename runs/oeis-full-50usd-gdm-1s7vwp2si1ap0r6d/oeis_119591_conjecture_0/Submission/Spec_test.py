import unittest
import subprocess

class TestSpec(unittest.TestCase):
    def test_no_sorry(self):
        # Run Lean on the Spec.lean file and capture stdout and stderr
        result = subprocess.run(
            ["lake", "env", "lean", "Submission/Spec.lean"],
            capture_output=True,
            text=True
        )
        
        output = result.stdout + result.stderr
        
        # Log the output for debugging
        print("\n--- Lean Compiler Output ---")
        print(output)
        print("----------------------------\n")
        
        # Assert that Lean compiler does not warn about the use of sorry
        self.assertNotIn("uses 'sorry'", output, "The solution contains 'sorry' and is incomplete!")
        
        # Assert that the file compiles successfully (exit code 0)
        self.assertEqual(result.returncode, 0, f"Compilation failed with exit code {result.returncode}")

if __name__ == '__main__':
    unittest.main()
