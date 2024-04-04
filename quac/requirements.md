collect and resolve typing constraints in module

parameters:

module node
callable node mappings

create new node callback

get_runtime_terms_callback
update_runtime_terms_callback
update_bag_of_attributes_callback
add_subset_callback

add relation callback

handle function call

parameters:
called function
callable node mappings
parameter node list
return value node

1. retrieve called function
2. if that function is defined within, execute handle user-defined function callback
3. if it is not, execute handle external function callback

handle attribute access

parameters:

runtime term
attribute

separate these two parts out first

(use another function: get accessed term)

