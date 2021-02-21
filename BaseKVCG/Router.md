# Router

## Current Design

The router utilizes a policy to decide whether a key is hot or cold.
This policy is a function f mapping the key to a boolean value.
Ideally f maps a key to be hot if it has a higher access rate than a
cold value.

There are two current policies implemented. One takes any key less than
a value and sends it to the CPU. This is good if the distribution takes
accesses smaller valued keys more than higher valued keys.

The other policy takes the function to buckets which are estimations of the probability of access of ranges of keys. To simplify this problem, a hash is initially used on the key and then ranges of hashes are put into buckets. This is fine with a 64 bit hash as the probability of colision is 1/2^64.

When the router is changed, updates are queued and the log in the CPU hashmap is flushed to the GPU hashmap. This allows for linearizability after the CAS of the log and map occurs. Once updates occurs a miss is never an issue, if it is still hot, nothing has changed. If it has changed from hot to cold, there is no issue because it will be linearized by the GPU hashmap.
