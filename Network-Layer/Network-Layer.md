# Network Layer

We are likely going to be assuming partial synchrony of the network.

This means that there exists a global stabalization time set by an adversary and a bound on the time it takes for communication in the network. We assume the global stabilization time occurs and a message must either arrive within the bound or within the bound after the global stabilization time.

## Planned contributions

- RPC API
- Distributed Shared Memory API for one-sided operations
- Broadcast primitives
- Failure detection
- GPUDirect Use

These are the ways the APIs should look.

RPC:

```c++
struct Server {
    void registerFunction(uint64_t id, fn_t function);
};

struct Client {
    void callFunction(uint64_t id, data_t data);
};
```

Distributed Shared Memory:

```c++
remote_mem.load();
remote_mem.store(x);
remote_mem.compare_and_swap(x,y);
```

Broadcast Primitives:

```c++
nodes.reliable_broadcast(message);
```

Failure Detection:

```c++
void register_failure_callback(fn_t callback);
```

## Current Work

- RPC API with perfect link guarentees.
  - Utilizes libfabric.
