# Network Layer

We are likely going to be assuming partial synchrony of the network.

This means that there exists a global stabalization time set by an adversary and a bound on the time it takes for communication in the network. We assume the global stabilization time occurs and a message must either arrive within the bound or within the bound after the global stabilization time.

## Contributions

We have a reliable connection based API that supports read, write, send, and recv.

This is specified in theories/networklayer.v
