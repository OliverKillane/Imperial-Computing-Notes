#!/bin/python3.11

from random import shuffle

# Creates the xml required for the hoare partitioning diagram
# in drawio: extras > edit diagram
# <mxGraphModel dx="886" dy="531" grid="1" gridSize="10" guides="1" tooltips="1" connect="1" arrows="1" fold="1" page="1" pageScale="1" pageWidth="827" pageHeight="1169" math="1" shadow="0">
#   <root>
#     <mxCell id="0" />
#     <mxCell id="1" parent="0" />
#     ... paste here ....
#   </root>
# </mxGraphModel> 

glob_id: int = 66

def for_ind(value: int, row: int, column: int, highlight: bool) -> None:
    position_column = column * 10
    position_row = row * 10
    
    col_v = int('FF', 16) // 64 * (value + 1)
    col_a = hex(col_v)[2:].zfill(2)
    
    if value > 32:
        colour = 'FF0000'
    elif value == 32:
        colour = col_a + '00' + col_a
    else:
        colour = '0000FF'
    
    global glob_id
    
    thick_boundary = "strokeWidth=3;" if highlight else ""
    print(f"""
<mxCell id="4u-d4tssBeN9KKuxx04D-{glob_id}" value="" style="rounded=0;whiteSpace=wrap;html=1;fillColor=#{colour};{thick_boundary}" vertex="1" parent="1">
      <mxGeometry x="{position_column}" y="{position_row}" width="10" height="10" as="geometry" />
</mxCell>""")
    glob_id += 1

def print_all(nums: list[int], depth: int, left_ptr: int | None = None, right_ptr: int | None = None) -> None:
    for x, i in enumerate(nums):
        for_ind(i, depth, x,  x == left_ptr or x == right_ptr)

def swap(l: list, x: int, y: int):
    a, b = l[x], l[y]
    l[x] = b
    l[y] = a


def diagram() -> None:
    nums = list(range(64))

    shuffle(nums)
    print_all(nums, 0)

    pivot_index = nums.index(32)
    pivot = nums[pivot_index]
    swap(nums, pivot, pivot_index)

    print_all(nums, 1)
    depth = 2
    left_i = 0
    right_i = 63

    while (left_i < pivot and right_i > pivot):
        while(nums[left_i] <= pivot):
            left_i += 1

        while(nums[right_i] > pivot):
            right_i -= 1

        if (left_i < pivot and right_i >= pivot):
            swap(nums, left_i, right_i)
            print_all(nums, depth, left_i, right_i)
            depth += 1
            left_i += 1
            right_i -= 1

diagram()








