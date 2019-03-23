#!/usr/bin/env python3
# -*- coding: utf-8 -*-

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
---- p_k = [x, y] 
---- circle_event = coordinate, False 

- Edges 
- Edges = [ [(p_k, p_l), [start, end] ], ...]
-- (pj_k, p{j+1}_l) its and edge between these two arcs
-- end can be None untill it is discovered by a circle event.
- edges = [(start, end), ...] we may add the sites that they seperate.

- Queue:
- Q = [site_event, or circle_event] ordered by y-coordinate of the focal point
-- site_event = pj = [xj, yj]
-- circle_event = circumcenter | False  

- Sweeplines 
-- if event = [[x0,y0], ...], or [x0, y0] then the sweepline is y = y0 
"""

# ------Auxiliaries Functions---------------#

def parabolas_intersection(p1, p2, y0):
    from math import sqrt
    """
    INPUT: pi = [xi, yi]
    
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



def check_circle_event( p, middle, right):
    """ p is the last found site. There will be a site event iff the 
    lowest point of the circle that touches p , right, left is below/on 
    the sweepline. In our case, we assume the sweep-line just touched p. 
    
    Note: This method will cover also the case where the vertical line, 
    from p to the  beachline, touches a breakpoint. 
    --------------------
    INPUT: pi, left, right = [xi, yi], [xl, yl], [xr, yr] 
          """
    
    c = circumcenter(p, middle, right)
    radius_sq = (c[0] - p[0])**2   + (c[1] - p[1])**2
    #the y-coordinate of project(c) onto the sweepline is p[1]
    #the lowestpoint b = c + radius is below/on y = p[1] iff 
    #c[1] + radius <= p[1] <==> radius_sq <= (p[1] - c[1])**2
    
    if  radius_sq <= (p[1] - c[1])**2 : #the y-coordinate
        return c
    #else:
    return False 


def search_edge(Edges, x_pos):
    #TODO: the list is an ordered list, use this fact!
    """INPUT: 
        Edges as in the preamble
        site = site_event
       OUTPUT: the indices of edges where the vertical line passes betweeen
       them. 
       
       arc_1 | arc_2 | arc_3 | ... | arc_n 
                 ^
                 |
               site     -x-> axes
       """
  
    n = len(Edges)
    if n == 0: 
        return 0
    for i in range(n):
        p, q = Edges[i][0], Edges[i][1]
        x = parabolas_intersection(p, q, x_pos)
        if x_pos <= x:
            return i
    return n-1 #the left most


def search_vertical(beachline, site):
    #TODO: the list is an ordered list, use this fact!
    """INPUT: 
        beachline as in the preamble
        site = site_event
       OUTPUT: the index/indices of arcs where the vertical line passes through
       arc_1 | arc_2 | arc_3 | ... | arc_n 
                 ^
                 |
               site     -x-> axes
       """
  
    n = len(beachline)
    x_site = site[0]
    
    if n == 1: 
        return [0]
    for i in range(n-1):
        p, q = beachline[i], beachline[i+1]
        x = parabolas_intersection(p[0], q[0], site[1])
        if x_site < x:
            return [i]
        if x_site == x:
            [i, i+1]
    return [n-1] #the left most
    

def vertical_intersection(parabola, point):
    """ The parabola is given by its focal point where the directrix is 
    y = point[1]. This function returns the intersection of the vertical line, 
    passes through point,  and the parabola. 
    --------------------
    INPUT: pi = [xi, yi] """
    
    px, py = parabola # unpack them
    x0, y0 = point
    return ( (px-x0)**2+ py**2   - y0**2)/( 2*(py - y0) )
        
    
def lines_intersection(l1, l2):
    """INPUT:
        l1 : a1x+b1y+c1 = 0
       l2 : a2x+b2y+c2 = 0 
       l1 is in the form: [ (a1, b1), c1] """
       
    a1, b1 = l1[1][0], l1[1][1]
    a2, b2 = l2[1][0], l2[1][1]
    c1, c2 = -l1[0], -l2[0]
    #by Cramer's rule 
    x = (c1*b2 - b1*c2) / (a1*b2 - b1*a2)
    y = (a1*c2 - c1*a2) / (a1*b2 - b1*a2)
    return (x, y)
       

def circumcenter(p1, p2, p3): 
    """ compute the circumcenter
    INPUT: pi = [xi, yi]"""
    
    # no check for collinearity as they define a circle event! 
    # auxiliaries functions 
    midpoint = lambda p1, p2 : ( (p1[0]+p2[0])/2,   (p1[1]+p2[1])/2 ) 
    direction = lambda p1, p2 : ( (p1[0]-p2[0]),   (p1[1]-p2[1]) ) 
    inner_product = lambda x, y: -sum( [x[i]*y[i] for i in range(len(x))]) #of the same length
    # l = n . (X - X0) = 0 => n.X0 = n.X
    line = lambda normal, point: (inner_product(normal, point), normal)
     
    midp1p2 = midpoint(p1, p2)
    midp2p3 = midpoint(p2, p3)
    # midp1p3 = midpoint(p1, p3) #no needs for this line
    # normal bisectors of pi, pj
    bisectp1p2 = line(direction(p1, p2), midp1p2) 
    bisectp2p3 = line(direction(p2, p3), midp2p3)
    # bisectp1p3 = line(direction(p1, p3), midp1p3)
    # As two lines intersect in one point
    c = lines_intersection(bisectp1p2, bisectp2p3) #two lines intersect in 
    return c
    
# ----------------END-----------------------#


def vor_diag(sites):
    #initialize
    #Q, beachline, voronoi
    Q, beachline, Edges = sites, [], []
    #sort Q according to the y-coordinate 
    Q.sort(key = lambda cord : cord[1])
    
    beachline = [[Q.pop(0), False]] #no circle event yet
    
    while Q: #not empty
        event = Q.pop(0) #Q = [a, b, c] --> event = a ,   Q = [b, c]
    
        if len(event) == 2: 
            beachline, Edges, Q = handle_site(event, beachline, Edges, Q )
            Q.sort(key = lambda cord : cord[1])
        else : 
            beachline, Edges, Q = handle_circle(event, beachline, Edges, Q)
    return Edges


    


    
def handle_site(event, beachline, Edges, Q):
    """we assume the beachline is not empty since we handled an event
    INPUT: event = [xj, yj]
           beachline as in the preamble
    """
    
    #arc_above index in the beachline
    arc_above  = search_vertical(beachline, event)

    
    if type(arc_above) == 2: #when the new sites intersects two arcs
        i = arc_above[0]
        p1, p2 = beachline[i][0], beachline[i+1][0]
        #position is a vertex
        position = parabolas_intersection(p1, p2, event[1])
        edg_ind = search_edge(Edges, position)
        Edges[edg_ind] = [Edges[edg_ind][0], [Edges[edg_ind][1][0], position ]] 
        Edges.insert(edg_ind,  [[event, p2],[position, None]] )#right
        Edges.insert(edg_ind,  [[p1, event],[position, None]] )#left
        beachline.insert(i+1, [event, None])

        return beachline, Edges, Q
    
    #Is there a false alarm?
    if arc_above[-1] != False: arc_above[-1] = False 
    ind = arc_above[0] #beachline[ind] returns [site, circle_event]
    #x-coordinate of the vertical intersection
    position = vertical_intersection(beachline[ind][0], event)
    #the index of the edge that comes before position
    edg_ind = search_edge(Edges, position)
    site = beachline[edg_ind][0] #the focal of the arc that has been broken
    Edges.insert(edg_ind,  [[event, site],[position, None]] )
    Edges.insert(edg_ind,  [[site, event],[position, None]] )
    

        
    #Add two arcs to the beach line
    # Index:     i         i,i+1,i+2
    #          \old/  to   \o/\n/\o/ , o: old, n: new
    #           ---         -  -  -
    beachline.insert(ind, [event, None])
    beachline.insert(ind+2, [event, None])
    
    #check for circle events
    # TODO wrong indices as they return the same arc
    # TODO  when there are not enough arc to get a circle event
    p_middle, p_right = beachline[ind+1][0], beachline[ind+2][0]
    if check_circle_event(event, p_middle, p_right):
        c = circumcenter(event, p_middle, p_right)
        beachline[i][1] = (event, p_middle, p_right)
        Q.append([p_middle, c]) 
    #right most
    p_left, p_middle = beachline[i-2][0], beachline[i-1][0]
    if check_circle_event(event, p_left, p_middle):
        c = circumcenter(event, p_left, p_middle)
        beachline[i][1] = (event, p_left,  p_middle)
        Q.append([p_middle, c]) 


    
def circle_even_init(left, middle, right, Q):
    """INPUT left, middle, right are focals of parabolas
    i.e. left = p_k = [xk, yk]
    Q is the Queue event. Sorting is local so we need to preform it outside"""
    
    c = check_circle_event(left[0], middle[0], right[0])
    if c: #python treats numbers as true
        middle[1] = True
        Q.append([middle[0], c])

    
def handle_circle(event, beachline, Edges, Q):
    #Search for the exact index
    for i in range(len(beachline)): 
        if beachline[i][0] == event[0]: ind = i
    #set the circle event for the two neighboring arcs to false
    c = event[1] #the circumcenter
    left, right = beachline[ind-1][1], beachline[ind+1][1] 
    left[1], right[1] = False
    
    #find the corresponding edge
    for i in range(len(Edges)): 
        if Edges[i][0] == [left, event]:
            ind_edge = i
    left_edge, right_edge = Edges[ind_edge], Edges[ind_edge+1]
    left_edge[1][1], right_edge[1][1] = c, c
    
    #check for a circle event finally
    left, right = beachline[i-1], beachline[i+1]
    left_left, right_right = beachline[i-2], beachline[i+2]
    circle_even_init(left_left[0], left[0], right[0], Q)   
    circle_even_init(left[0], right[0], right_right[0], Q)

if __name__ == '__main__':
    #test sties
    sites = [[23, 8], [87, 14], [72, 18], [73, 30], [25, 43], [93, 51], [65, 54], [81, 61], [65, 65], [5, 67], [44, 70], [15, 74], [31, 81], [30, 82], [15, 89], [35, 96], [23, 98], [19, 99]]
    vor_diag(sites)
    #ordered sites
    #[[23, 8], [87, 14], [72, 18], [73, 30], [25, 43], [93, 51], [65, 54],
    # [81, 61], [65, 65], [5, 67], [44, 70], [15, 74], [31, 81], [30, 82], 
    # [15, 89], [35, 96], [23, 98], [19, 99]]