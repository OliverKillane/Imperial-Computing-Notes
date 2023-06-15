from dataclasses import dataclass


@dataclass
class SortState:
    pivot: int
    cmp: bool
    active: int
    backup: int
    left_ptr: int
    right_ptr: int
    data: list[int]

    def __str__(self):
        data_strs = list(map(str, self.data[0 : self.left_ptr]))
        if self.left_ptr < self.right_ptr:
            data_strs += (
                [f"({self.data[self.left_ptr]})"]
                + list(map(str, self.data[self.left_ptr + 1 : self.right_ptr]))
                + [f"({self.data[self.right_ptr]})"]
            )
        else:
            data_strs += [f"({self.data[self.left_ptr]})"]
        data_strs += list(map(str, self.data[self.right_ptr + 1 :]))
        return f"""piv cmp act bak
 [{self.pivot}] [{int(self.cmp)}] [{self.active}] [{self.backup}]
 [{",".join(data_strs)}]\n"""


def start_state(data: list[int], pivot: int) -> SortState:
    return SortState(
        pivot=pivot,
        cmp=False,
        active=data[0],
        backup=data[-1],
        left_ptr=0,
        right_ptr=len(data) - 1,
        data=data,
    )


def compare_and_write_phase(s: SortState):
    """
    We already have ACTIVE and BACKUP, we can safely overwrite their
    positions in the list and set CMP
    """
    s.cmp = s.pivot > s.active
    s.data[s.left_ptr] = s.active
    s.data[s.right_ptr] = s.active


def advance_cursor_phase(s: SortState):
    """
    CMP is True/1  -> only advance the left
    CMP is False/0 -> only advance the right
    """
    s.left_ptr += s.cmp
    s.right_ptr -= 1 - s.cmp


def backup_phase(s: SortState):
    """
    We want the new active value, we can use CMP to work out which pointer got
    advanced, and hence which value to read into active
    """
    s.active = (s.cmp * s.data[s.left_ptr]) + ((1 - s.cmp) * s.data[s.right_ptr])


def swap_active_backup_phase(s: SortState):
    """
    Finally we swap the active and backup, and now place & compare the backup
    """
    s.active, s.backup = s.backup, s.active


def place_active(s: SortState):
    assert s.left_ptr == s.right_ptr
    s.data[s.left_ptr] = s.active


def partition_predicated(data: list[int], pivot: int):
    s = start_state(data, pivot)
    print("START:\n", s)
    step = 1
    while s.left_ptr < s.right_ptr:
        print(f"STEP {step}:")
        compare_and_write_phase(s)
        print(f"{step}a COMPARE & WRITE:\n{s}")
        advance_cursor_phase(s)
        print(f"{step}b ADVANCE CURSOR:\n{s}")
        backup_phase(s)
        print(f"{step}c BACKUP:\n{s}")
        swap_active_backup_phase(s)
        print(f"{step}d SWAP ACTIVE & BACKUP:\n{s}")
        step += 1
    place_active(s)
    print("FINAL LIST:\n", s)


# partition_predicated([3, 2, 4, 2, 8, 1, 9, 3, 8, 1, 5, 0, 7, 5, 7], pivot=5)
# partition_predicated([0, 1, 5, 8, 9], pivot=5)
partition_predicated([10, 10, 10, 0], pivot=3)
