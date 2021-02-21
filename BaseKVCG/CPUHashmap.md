# CPU Hashmap

## Current Design

The CPU hashmap is currently a chained array hashmap with readers-writer locks.

There is a place in a log associated with each element. On a write the log is written to.

Reads aquire shared locks on the hashmap.

Misses on the hashmap are sent to the GPU.

## High Level Spec

The map is linearizable.

Without misses, a batch of operations occurs in order from the 0th element to the last.

On a miss, the operation is sent to the GPU and will return the last write if the key is in a quiescent state, otherwise it will return the most recent write at its linearization point (when the insert done by the GPU handling thread fails).
