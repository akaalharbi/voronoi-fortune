#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from avl import AVL, AVLNode
from dcel import DCEL
from copy import deepcopy
"""
Created on Mon Mar 18 17:44:50 2019

An implementation of "Algorithm VORONOI DIAGRAM (P)" in Computational Geometry:

Data structures:
beachline := balanced binary tree, leaf := [site, (x,y)-circle-event | None ]
                                   node := [(p_i, p_j), half-edge-name]
Q := [event: for an event in events] #sorted by y-coordinate
event = a site::=[x,y] or circle-event::=[x, y, True]
half-edge = [beginning, end] 
Edges = {name: half-edge, ... }
"""


def vor_diag(sites):
    #initialize
    #Q, beachline, voronoi
    Q, beachline, voronoi = sites, AVL(), dict([])
    #sort Q according to the y-coordinate 
    Q.sort(key = lambda cord : cord[1])
    
    
    while Q: #not empty
        #event
        event = Q.pop(0) #Q = [a, b, c] --> event = a ,   Q = [b, c]
    
        if len(event) == 2: #only site=(x, y), no indication of a circle-event 
            beachline, voronoi = handle_site(event, beachline, voronoi )
        else : 
            beachlin, voronoi = handle_circle(event, beachline, voronoi)
    return voronoi

def handle_site(event, beachline, voronoi):
    """we assume the beachline is not empty since it was handled before"""
    arc_above = search_vertical(event, beachline)
    #False alarm
    if arc_above[-1] == True: arc_above[-1] = False 
    #Find the arc position and its parent
    arc_leaf = beachline.find(arc_above) #the leaf in the tree
    parent = arc_leaf.parent 
    #arc.key[0]= p_i, event = p_j. Half-edges will be in the place of None 
    edge_left, edge_right = [(arc.key[0], event), None ],\
                            [(event, arc.key[0]), None ]  
    #add half-edge
    
    #create new subtree
    #  parent        parent 
    #    |             |
    #   arc -tr->     edge_left  
    #                 / \
    #               arc  edge_right
    #                        /  \
    #                    event  arc #the event is the new site
    edge_left = AVLNode(parent, edge_left ),\  
    edge_right, arc_leaf.parent = AVLNode(edge_left, edge_right) edge_right
    arc_leaf_right = deepcopy(arc_leaf)
    arc_leaf_right.parent = edge_right
    arc_leaf_right.right, arc_leaf_right.left  = None, None
    
    
    #check if there will be a circle event
    #two points from left half-edge
    #two points from right half-edge
    # compute l1, l2
    # find the intersection if it below the beachline then it's a circle event
    # else pass
    
    
def handle_circle(eventevent, beachline, voronoi):
    pass


def search_vertical(beachline, site):
    pass

def lines_intersection(l1, l2):
    """l1 : a1x+b1y+c1 = 0
       l2 : a2x+b2y+c2 = 0 
       l1 is in the form:
                  [ (a1, b1), c1]"""
       
       a1, b1 = l1[0]
       a2, b2 = l2[0]
       c1, c2 = l1[1], l2[1]
       #by Cramer's rule 
       x = (c1*b2 - b1*c2) / (a1*b2 - b1a2)
       y = (a1*c2 - c1*a2) / (a1*b2 - b1a2)
       return (x, y)
       

def circumcenter(p1, p2, p3): 
    """ compute the circumcenter"""
    #no check for collinearity as they define a circle event! 
    #auxiliaries functions 
    midpoint = lambda p1, p2 : ( (p1[0]+p2[0])/2,   (p1[1]+p2[1])/2 ) 
    direction = lambda p1, p2 : ( (p1[0]-p2[0]),   (p1[1]-p2[1]) ) 
    inner_product = sum( [x[i]*y[i] for i in range(len(x))]) #of the same length
    #l = n . (X - X0) = 0 => n.X0 = n.X
    line = lambda normal, point: (normal, inner_product(normal, point))
     
    midp1p2 = midpoint(p1, p2)
    midp2p3 = midpoint(p2, p3)
    midp1p3 = midpoint(p1, p3)
    #normal bisectors of pi, pj
    bisectp1p2 = line(direction(p1, p2), p1) #just wanted to use midp1p2
    bisectp2p3 = line(direction(p2, p3), p2)
    #bisectp1p3 = line(direction(p1, p3), p3)
    #As two lines intersect in one point
    c = lines_intersection(bisectp1p2, bisectp2p3) #two lines intersect in 
    return c
    