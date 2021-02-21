# GPU Hashmap

## Current Design

Currently the GPU hashmap utilizes a warp-cooperative lock based approach. This approach stems from Slab. This was chosen for coalescence and how warp-cooperation limits contention.

The hashmap pipeline focuses on minimizing the impact of the PCIe latency which can cause issues for both multi-GPU scalability and performance.

The pipeline has the GPU take a batch of requests, send it to the GPU over PCIe, run the requests, and send it back to the CPU. Once on the CPU the results are written back to the client or put in the CPU map if need be.

## High Level Spec

For a single stream pipeline, the GPU maintains linearizability by ensuring that the prior kernel's operations occur before the current kernel's operations.

The currents kernel's operations can be ordered in any possible linearizable schedule.

When responding, if a read is a miss, it will insert the result into the CPU map. If the there has been an update to the CPU hashmap, the client recieves the update rather than the GET performed on the GPU.

## Considered alternatives

GPU-Direct copy may improve the performance of the GPU with respect to the PCIe bus, but requires specific GPUs.
