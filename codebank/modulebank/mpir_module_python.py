import sys

# Get the command line arguments
arguments = sys.argv

# The first element (index 0) is the script name
script_name = arguments[0]

# The rest of the elements are the command line arguments
command_line_arguments = arguments[1:]

# Print the results
print("Script name:", script_name)
print("Command line arguments:", command_line_arguments)
