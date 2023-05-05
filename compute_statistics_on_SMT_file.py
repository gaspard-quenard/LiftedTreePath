import argparse

def compute_statistics_on_SMT_file(file: str):

    with open(file, 'r') as f:
        lines = f.readlines()
        lines = [line.strip() for line in lines]

    # First, determinate the number of actions
    # Each action is determinate with a line: (declare-const FLOW_

    actions = [line for line in lines if line.startswith('(declare-const FLOW_')]


    # Then determiane the number of scopes 
    # Each scope is determinate with a line: (declare-const SCOPE_, but should not contains __eq__ in the line

    scopes = [line for line in lines if line.startswith('(declare-const SCOPE_') and '__eq__' not in line]

    scope_equality = [line for line in lines if line.startswith('(declare-const SCOPE_') and '__eq__' in line]

    # Then determinate the number of unique scope (from the scopes variable)
    # Each unique scope is determinate with a line: (declare-const SCOPE_<ID_scope>

    unique_scopes = set()
    for scope_line in scopes:
        name_scope = scope_line.split(' ')[1].split('__')[0]
        unique_scopes.add(name_scope)

    # Print the results
    print('Number of actions: {}'.format(len(actions)))
    print('Number of scopes: {}'.format(len(scopes)))
    print('Number of unique scopes: {}'.format(len(unique_scopes)))
    print('Number of scope equality: {}'.format(len(scope_equality)))



if __name__ == '__main__':
    
    parser = argparse.ArgumentParser()
    parser.add_argument('--file', type=str, required=True, help='Path to the SMT file')
    args = parser.parse_args()

    compute_statistics_on_SMT_file(args.file)