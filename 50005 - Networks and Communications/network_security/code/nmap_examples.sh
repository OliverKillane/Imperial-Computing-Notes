# Quick scan without checking ports
nmap -sn <ip address>

# Scan a range of ports on a host
nmap -p <start port>-<end port> <ip address>

# Scan all ports on a host
nmap -p- <ip address>

# Scan without discovery (even if the host wont respond to a ping, we can still check its ports)
nmap -Pn <ip address>
