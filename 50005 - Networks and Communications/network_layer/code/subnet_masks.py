# Super basic IP mask creation, string conversions and range.
from typing import Tuple

def ipv4_to_str(ip: int) -> str:
    assert(0 <= ip < 2**32)
    return ".".join([str((ip // (2**(8 * i))) % 256) for i in range(3,-1,-1)])

def get_mask(prefix_len: int) -> int:
    return (2**(prefix_len+1) - 1) * 2 **(32 - prefix_len)

def get_ipv4(ip: str) -> int:
    ip = ip.split(".")
    assert(len(ip) == 4)
    ip_num = 0
    for sub in map(int, ip):
        ip_num *= 256
        assert(0 <= sub < 256)
        ip_num += sub
    return ip_num

def apply_mask(ip: str, mask: int) -> str:
    return ipv4_to_str(get_ipv4(ip) & get_mask(mask))

def get_range(ip: str, mask: int) -> Tuple[int, int]:
    ip = get_ipv4(ip)
    subnet_mask = get_mask(mask)

    return (ip & subnet_mask | ((2**32 -1 ) & (~subnet_mask)), ip & subnet_mask)

# Example code
# print(apply_mask(input("Input IP:  "), int(input("Prefix:    "))))
# (bot, top) = get_range(input("Input IP:  "), int(input("Prefix:    ")))
# print(f"From {ipv4_to_str(top)} to {ipv4_to_str(bot)}")