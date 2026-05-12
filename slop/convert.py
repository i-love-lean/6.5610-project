import re

def convert_lisp_code(input_file, output_file=None):
    """
    Convert Lisp code from !(def name ...) format to (name ...) format
    """
    
    # Read the input file
    with open(input_file, 'r') as f:
        code = f.read()
    
    # Normalize whitespace while preserving structure
    lines = code.split('\n')
    
    results = []
    i = 0
    
    while i < len(lines):
        line = lines[i].strip()
        
        # Skip empty lines
        if not line or ";" in line:
            i += 1
            continue
        
        # Collect lines until we have a complete definition
        if line.startswith('!'):
            full_def = line[1:]  # Remove the !
            
            # Count parentheses to know when definition is complete
            paren_count = full_def.count('(') - full_def.count(')')
            
            # Keep adding lines until parentheses are balanced
            j = i + 1
            while paren_count > 0 and j < len(lines):
                if ";" not in lines[j]:
                    full_def += ' ' + lines[j].strip()
                    paren_count += lines[j].count('(') - lines[j].count(')')
                j += 1
            
            # Parse the definition
            match = re.match(r'\((def|defrec)\s+(\S+)\s+(.*)\)$', full_def)
            
            if match:
                name = match.group(2)
                body = match.group(3)
                results.append(f"({name} {body})")
            else:
                # Fallback - just remove ! and def/defrec if pattern doesn't match
                results.append(full_def)
            
            i = j
        else:
            i += 1
    
    # Write output
    output_text = '\n'.join(results)
    
    if output_file:
        with open(output_file, 'w') as f:
            f.write(output_text)
        print(f"Converted code written to {output_file}")
    else:
        print(output_text)
    
    return output_text


# Usage
if __name__ == '__main__':
    # Replace 'input.lisp' with your input file name
    convert_lisp_code('dependent.lurk', 'out.lurk')
