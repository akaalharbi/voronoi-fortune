#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from avl import AVL, AVLNode
#from dcel import DCEL
from copy import deepcopy
"""
Created on Mon Mar 18 17:44:50 2019

An implementation of "Algorithm VORONOI DIAGRAM (P)" in Computational Geometry:
DIRECTION: The sweepline moves downward

Data structures:
- Beachline:
-- Walk from the left to the right and record every arc you see with extra info.
-- beachline' := [p1_i, p2_l, p3_k, ...] where pj_i means the j-th arc which is
-- part of a parabola that has p_i as its focal point.
--- pj_k = [p_k, circle_event] 
---- circle_event = coordinate, False 
- Edges 
- Tracing = [ [(pj_k, p{j+1}_l), [start, end] ], ...]
-- (pj_k, p{j+1}_l) its and edge between these two arcs
-- end can None untill 
e.g. [p1_2, p_1, p_2,] i.e. enountered p_2, then p_1, and finally p_2    
p_i = [focal ]    

beachline := balanced binary tree, leaf := [site, (x,y) if circle-event or None ]
                                   node := [(p_i, p_j), edge-index]

Edges = [l, edge] #either an equation or a line 
Q := [event: for an event in events] #sorted by y-coordinate
event = a site::=[x,y] or circle-event::=[x, y, True]
UPDATE: When we start tracing a new line segment l, we add the start point s
        and we store l equation (as an infinite line). If we encounter the end 
        point e of l, we replace the line's equation with segment. 
segment = set([x0, y0], [x1, y1])  or line [[x0, y0], [n0, n1]]      

When 
"""

def check_circle_event( p, right, left):
    """ p is the last found site. There will be a site event iff the 
    lowest point of the circle that touches p , right, left is below/on 
    the sweepline. In our case, we assume the sweep-line just touched p. 
    
    Note: This method will cover also the case where the vertical line, 
    from p to the  beachline, touches a breakpoint. """
    
    c = circumcenter(p, right, left)
    radius_sq = (c[0] - p[0])**2   + (c[1] - p[1])**2
    #the y-coordinate of project(c) onto the sweepline is p[1]
    #the lowestpoint b = c + radius is below/on y = p[1] iff 
    #c[1] + radius <= p[1] <==> radius_sq <= (p[1] - c[1])**2
    
    if  radius_sq <= (p[1] - c[1])**2 : #the y-coordinate
        return c
    #else:
    return False 


def vor_diag(sites):
    #initialize
    #Q, beachline, voronoi
    Q, beachline, voronoi = sites, AVL(), dict([])
    #sort Q according to the y-coordinate 
    Q.sort(key = lambda cord : cord[1])
    voronoi = []
    
    while Q: #not empty
        #event
        event = Q.pop(0) #Q = [a, b, c] --> event = a ,   Q = [b, c]
    
        if len(event) == 2: #only site=(x, y), no indication of a circle-event 
            beachline, voronoi = handle_site(event, beachline, voronoi )
        else : 
            beachlin, voronoi = handle_circle(event, beachline, voronoi)
    return voronoi


def parabolas_intersection(p1, p2, y0):
    from math import sqrt
    """
    This expression was computed using SageMath. The result by hand is more 
    compact and computationally efficient (less number of multiplications) but
    it's prone to errors!
    -------SageMath--------------
    var('x y0 px1 py1 px2 py2  ')
    eq = ( (px1 - x)^2 + (py1 - y0 )^2  )/ (2*(py1-y0))  == ( (px2 - x)^2 + (py2 - y0 )^2  )/ (2*(py2-y0))
    solve(eq, x)
    --------END------------------
    """
    
    px1, py1 = p1
    px2, py2 = p2
    #y0 is the horizontal directrix 
    a = (px2*py1 - px1*py2 + (px1 - px2)*y0)
    b = (py1 - py2)
    disc = sqrt(-2*py1**2*py2**2 + py1*py2**3 + (px1**2 - 2*px1*px2 + px2**2 + py1**2 - 2*py1*py2 + py2**2)*y0**2 + (py1**3 + (px1**2 - 2*px1*px2 + px2**2)*py1)*py2 - (py1**3 - py1*py2**2 + py2**3 + (px1**2 - 2*px1*px2 + px2**2)*py1 + (px1**2 - 2*px1*px2 + px2**2 - py1**2)*py2)*y0)

    return (a+disc)/b    
    

def vertical_intersection(parabola, point):
    """ The parabola is given by its focal point where the directrix is 
    y = point[1]. This function returns the intersection of the vertical line, 
    passes through point,  and the parabola. 
    """
    px, py = parabola #unpack them
    x0, y0 = point
    return ( (px-x0)**2+ py**2   - y0**2)/( 2*(py - y0) )


    
def handle_site(event, beachline, voronoi):
    """we assume the beachline is not empty since it was handled before"""
    #TO DO!
    arc_above = search_vertical(event, beachline)
    
    #Is there a false alarm?
    if arc_above[-1] != False: arc_above[-1] = False 
    
    #Find the arc position and its parent
    arc_leaf = beachline.find(arc_above) #the leaf in the tree
    parent = arc_leaf.parent 
    #arc.key[0]= p_i, event = p_j. Half-edges will be in the place of None 
    #FIX ME! edge_left = [<pi, pj>, index-of-an-edge]
    edge_left, edge_right = [(arc_leaf.key[0], event), None ],\
                            [(event, arc_leaf.key[0]), None ]  
    #add half-edge
    
    #create new subtree
    #  parent        parent 
    #    |             |
    #   arc -tr->     edge_left  
    #                 / \
    #               arc  edge_right
    #                        /  \
    #                    event  arc #the event is the new site
    edge_left = AVLNode(parent, edge_left )  
    edge_right, arc_leaf.parent = AVLNode(edge_left, edge_right), edge_right
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
    #use the beachline and parabolas_intersectio
    pass

def lines_intersection(l1, l2):
    """l1 : a1x+b1y+c1 = 0
       l2 : a2x+b2y+c2 = 0 
       l1 is in the form:
[ (a1, b1), c1]"""
    a1, b1 = l1[1][0], l1[1][1]
    a2, b2 = l2[1][0], l2[1][1]
    c1, c2 = -l1[0], -l2[0]
    #by Cramer's rule 
    x = (c1*b2 - b1*c2) / (a1*b2 - b1*a2)
    y = (a1*c2 - c1*a2) / (a1*b2 - b1*a2)
    return (x, y)
       

def circumcenter(p1, p2, p3): 
    """ compute the circumcenter"""
    #no check for collinearity as they define a circle event! 
    #auxiliaries functions 
    midpoint = lambda p1, p2 : ( (p1[0]+p2[0])/2,   (p1[1]+p2[1])/2 ) 
    direction = lambda p1, p2 : ( (p1[0]-p2[0]),   (p1[1]-p2[1]) ) 
    inner_product = lambda x, y: -sum( [x[i]*y[i] for i in range(len(x))]) #of the same length
    #l = n . (X - X0) = 0 => n.X0 = n.X
    line = lambda normal, point: (inner_product(normal, point), normal)
     
    midp1p2 = midpoint(p1, p2)
    midp2p3 = midpoint(p2, p3)
    1#midp1p3 = midpoint(p1, p3) #no needs for this line
    #normal bisectors of pi, pj
    bisectp1p2 = line(direction(p1, p2), midp1p2) 
    bisectp2p3 = line(direction(p2, p3), midp2p3)
    #bisectp1p3 = line(direction(p1, p3), midp1p3)
    #As two lines intersect in one point
    c = lines_intersection(bisectp1p2, bisectp2p3) #two lines intersect in 
    return c
    