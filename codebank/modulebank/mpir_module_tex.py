import json

def read_and_print_json(file_path):
    try:
        # Open the JSON file for reading
        with open(file_path, 'r') as json_file:
            # Load the JSON data
            json_data = json.load(json_file)

            # Print the JSON data
            print(json.dumps(json_data, indent=2)) 

    except FileNotFoundError:
        print(f"Error: File not found at path: {file_path}")
    except json.JSONDecodeError as e:
        print(f"Error decoding JSON: {e}")


read_and_print_json("testj.json")