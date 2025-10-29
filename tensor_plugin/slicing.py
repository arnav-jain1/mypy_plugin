import itertools
import numpy as np


def remove_ellipses(input_shape, slice_tuple):

    # If there is more than 1 ellipsis, then there is an error
    if slice_tuple.count(Ellipsis) > 1:
        return -1
        
    # Get the index of the ellipsis and get items before and after
    ellipsis_idx = slice_tuple.index(Ellipsis)
    items_before = slice_tuple[:ellipsis_idx]
    items_after = slice_tuple[ellipsis_idx + 1:]
    
    # get amount of dims the ... is replacing (needs to be >= 0)
    num_replaced = (len(input_shape) - len(items_before) - len(items_after))
    
    if num_replaced < 0:
        return -1
        
    # replace the ... with : and return
    replaced = (slice(None),) * num_replaced
    
    return items_before + replaced + items_after

"""Handles the ints and replaces the non ints with a placeholder and adjusts the slice accordingly"""
def handle_int(input_shape, input_slice):
    output_template = []
    new_shape = []
    new_slice = []
    
    shape_idx = 0
    slice_idx = 0
    
    while slice_idx < len(input_slice) or shape_idx < len(input_shape):

        # Remove this when supporting None or np.newaxis
        if shape_idx >= len(input_shape):
            raise IndexError("Slice bigger than shape (None not yet supported)")
        
        current_dim = input_shape[shape_idx] 
        # This is the case if the shape is bigger than the slice, keep the unsliced dims the same
        current_slice = input_slice[slice_idx] if slice_idx < len(input_slice) else slice(None)
        
        # If the current dim is an int, then if the slice is an int then we can just remove the dim, otherwise the output will be an int
        if current_dim == int:
            if isinstance(current_slice, int):
                pass
            elif isinstance(current_slice, slice):
                output_template.append(int)
        
        # Change when adding None
        elif current_dim is not None:

            new_shape.append(current_dim)
            new_slice.append(current_slice)
            
            # If the slice is a slice, then skip over it for now
            if isinstance(current_slice, slice):
                output_template.append('PLACEHOLDER')
            elif isinstance(current_slice, int):
                pass
        
        
        shape_idx += 1
        if current_slice is not None:
            slice_idx += 1
            
    return output_template, new_shape, tuple(new_slice)


""" Generates all combinations of arrays"""
def generate(dims_to_test):
    iterables = []
    for dim in dims_to_test:
        if isinstance(dim, int):
            iterables.append((dim,))
        else:
            iterables.append(dim)
            
    for shape_tuple in itertools.product(*iterables):
        yield shape_tuple

"""Combines the shapes that work"""
def combine_shapes(shapes):
    if not shapes:
        return []
        
    dims = len(shapes[0])
    output = []
    
    for i in range(dims):
        dim = {shape[i] for shape in shapes}
        
        if len(dim) == 1:
            output.append(dim.pop())
        else:
            output.append(tuple(sorted(list(dim))))
            
    return output

def slice_output(input_shape, slice_tuple):
    print(slice_tuple)
    print(input_shape)
    
    # Make sure it is a tuple
    slice_tuple = slice_tuple if isinstance(slice_tuple, tuple) else (slice_tuple,)
    
    if Ellipsis in slice_tuple:
        slice_tuple = remove_ellipses(input_shape, slice_tuple)
        if slice_tuple == -1:
            raise IndexError("Ellipses error")


    placeholder, concrete, adj_slice = handle_int(input_shape, slice_tuple)
    
    possible_shapes = generate(concrete)
    
    success = []
    for shape in possible_shapes:
        temp = np.empty(shape, dtype=np.int8)
        
        try:
            result = temp[adj_slice]
            success.append(result.shape)
        except IndexError:
            # Shape doesnt work
            pass

    if not success:
        raise IndexError("Slice is invalid.")

    output_dims = combine_shapes(success)

    final_shape = []
    output_dim_idx = 0
    for item in placeholder:
        if item == 'PLACEHOLDER':
            final_shape.append(output_dims[output_dim_idx])
            output_dim_idx += 1
        else:
            final_shape.append(item)
            
    return final_shape if final_shape else int

if __name__ == '__main__':
    x = np.array([1, 2, 3, 4, 5, 6])
    
    test_slice = [Ellipsis, slice(None, None, None)]
    
    output_shape = slice_output([6], test_slice)
        
    print(f"Calculated output shape: {output_shape}")
        
    actual_output = x[test_slice]
    print(f"Actual NumPy output shape: {actual_output.shape}")