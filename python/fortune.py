#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Created on Mon Mar 18 17:44:50 2019

An implementation of "Algorithm VORONOI DIAGRAM (P)" in Computational Geometry:
DIRECTION: The sweepline moves upward

Data structures:

- Beachline:
-- Walk from the left to the right and record every arc you see with extra info.
-- beachline' := [p1_i, p2_l, p3_k, ...] where pj_i means the j-th arc which is
-- part of a parabola that has p_i as its focal point.
--- pj_k = [p_k, circle_event]
---- p_k = [x, y]
---- circle_event = [[l, m, r], m[1]] the three arcs with the y-coordinate of
                    the disappearing arc

- Edges
- Edges = [ [(p_k, p_l), [start, end] , boolean], ...]
-- (pj_k, p{j+1}_l) its and edge between these two arcs
-- end can be None untill it is discovered by a circle event.
-- boolean indicates it's a complete edge. This feature is for drawing.
- edges = [(start, end), ...] we may add the sites that they seperate.

- Queue:
- Q = [site_event, or circle_event] ordered by y-coordinate of the focal point
-- site_event = pj = [xj, yj]
-- circle_event = circumcenter | False

- Sweeplines
-- if event = [[x0,y0], ...], or [x0, y0] then the sweepline is y = y0
"""
from math import sqrt
# ------Auxiliaries Functions---------------#

def parabolas_intersection(p1, p2, y0):

    """
    Check: ok
    Warning: Pay attention to the left and right solution 
    INPUT: pi = [xi, yi]

    This expression was computed using SageMath. The result by hand is more
    compact and computationally efficient (less number of multiplications) but
    it's prone to errors!
    -------SageMath--------------
    var('x y0 px1 py1 px2 py2  ')
    eq = ( (px1 - x)^2 + (py1 - y0 )^2  )/ (2*(py1-y0))  == ( (px2 - x)^2 + (py2 - y0 )^2  )/ (2*(py2-y0))
    solve(eq, x)
    --------END------------------
    x = (a + sqrt(disc))/b ,  (a - sqrt(disc))/b
    """
    px1, py1 = p1
    px2, py2 = p2
    #y0 is the horizontal directrix
    a = (px2*py1 - px1*py2 + (px1 - px2)*y0)
    b = (py1 - py2)
    disc = -2*py1**2*py2**2 + py1*py2**3 + (px1**2 - 2*px1*px2 + px2**2 + py1**2 - 2*py1*py2 + py2**2)*y0**2 + (py1**3 + (px1**2 - 2*px1*px2 + px2**2)*py1)*py2 - (py1**3 - py1*py2**2 + py2**3 + (px1**2 - 2*px1*px2 + px2**2)*py1 + (px1**2 - 2*px1*px2 + px2**2 - py1**2)*py2)*y0
    return (a, disc, b)



def check_circle_event( l, m, r, y0):
    """ 
    Check: review
    l or r are the last found site. There will be a site event iff the
    lowest point of the circle that touches l , right, left is below/on
    the sweepline. In our case, we assume the sweep-line just touched p.
    y0 is the directrix.

    Note: This method will cover also the case where the vertical line,
    from p to the  beachline, touches a breakpoint.
    --------------------
    INPUT: left, middle, right = [xl yl], [xm, ym], [xr, yr]
          """
    
    
    
    
#    if collinear(l, m, r): return False 
#    c = circumcenter(l, m, r)
#    y  = c[1]
#    y0 = max(l[1], m[1], r[1])
#    radius_sq = (c[0] - l[0])**2   + (c[1] - l[1])**2
#    #the y-coordinate of project(c) onto the sweepline is l[1]
#    #the lowestpoint b = c + radius is above/on y = l[1] iff
#    #c[1] + radius <= l[1] <==> radius_sq <= (l[1] - c[1])**2
#    
#    if radius_sq >= (l[1] - c[1])**2 : #the y-coordinate
#        return c
    
    #else:
#    if y >= y0: return c
#    return False
    if collinear(l, m, r): return False
    ax, ay = l
    bx, by = m
    cx, cy = r
    
    # check if bc is a "right turn" from 
    if ((by - ay)*(cx - ax) - (cy - ay)*(bx - ax)) > 0: return False
    c = circumcenter(l, m, r) 
    radius   = sqrt((c[0] - m[0])**2   + (c[1] - m[1])**2)
    upper_point = [c[0], radius+c[1]]
    if upper_point[1] >= y0: 
        print(upper_point)
        return upper_point[1]


def search_edge(Edges, x_pos):
    #TODO: the list is an ordered list, use this fact!
    """ Check: ok
        INPUT:
        Edges as in the preamble
        site = site_event
       OUTPUT: the index of the edge that lies after x_pos or exactly at it.

       arc_1 | arc_2 | arc_3 | ... | arc_n
                 ^
                 |
               x_pos     -x-> axes
       """

    n = len(Edges)
    if n == 0:
        return None
    for i in range(n):
        p, q = Edges[i][0][0], Edges[i][0][1]
        
        sign = 1 if p > q else  -1
        a, disc, b = parabolas_intersection(p, q, x_pos)
        ineq = (b*x_pos - a)**2 
        
        if ineq <=  sign*disc:
            return i
        
    return n-1 #the left most


def parabola (p, y0):
    """
    p is the focla, y0 is the directrix"""
    
    x1, y1 = p
    return lambda x: ((x-x1)**2 + y1**2 - y0**2) / 2*(y1-y0)

def up(a, d, b):
    """Returns the sign of the larger solution"""
    s1, s2 = (a+sqrt(d))/b, (a-sqrt(d))/b
    if s1 > s2: return 1
    else: return -1

def before(p1, p2, p):
    """ Check: not ok!
    two case:
    break  |      
        p1 | p2   
        \_/*\_/    
         ^             
         |        
         p        
    Where is p? is it before the break point *?
    OUTPUT: [i, flag]   
            * i := False when p is on the right of *
            * i := True when p is on the left  of * 
            * flag :=  True when p is exactly on the same vertical line as *
            * flag := False otherwise """
    x_site, y_site = p
    a, disc, b = parabolas_intersection(p1, p2, y_site)
    # TODO: get rid of the square root, and hadnle the signs carefully 
    s1, s2 = (a+sqrt(disc))/b, (a-sqrt(disc))/b
    left, right = min(s1, s2), max(s1, s2) 
    # if p1 was discovered first, by the sweepline, then we take the minimum
    # solution, else we take the maximum.
    
    if (p1[1], p1[0]) < (p2[1], p2[0]):
        star = left
    else: star = right
#    cond_left = left > x_site
#    cond_right = right < x_site
#    cond_middle =  (left <  x_site) and (right > x_site)
    equality =  abs(star - x_site) < 0.00001 #almost equal
    
    if star > x_site:
        return [True, False]
    if equality:
        return [True, True]
    return [False, False]

def search_vertical(beachline, site):
    #TODO: the list is an ordered list, use this fact!
    """ Check: review
        INPUT:
        beachline as in the preamble
        site = site_event
       OUTPUT: the index/indices of arcs where the vertical line passes through
       arc_1 | arc_2 | arc_3 | ... | arc_n
                 ^
                 |
               site     -x-> axes
       """
       
    n = len(beachline)

    if n == 1:
        return [0]
    i = 0 #index of the arc
    while i <  n-1:
        p, q = beachline[i], beachline[i+1]
        is_before, flag = before(p[0], q[0], site)
        if is_before and flag:
            return [i, i+1]
        if is_before and not flag:
            return [i]
        i += 1
         
    return [n-1] #the right most


def vertical_intersection(parabola, point):
    """ Check: 
    The parabola is given by its focal point where the directrix is
    y = point[1]. This function returns the intersection of the vertical line,
    passes through point,  and the parabola.
    --------------------
    INPUT: pi = [xi, yi] """

    px, py = parabola # unpack them
    x0, y0 = point
    return ( (px-x0)**2+ py**2   - y0**2)/( 2*(py - y0) )


def lines_intersection(l1, l2):
    """ Check: ok
    INPUT:
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
    """ Check: ok
    compute the circumcenter
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
        if event == [59, -85]: 
            print("pay attention to me!")
        if type(event[0]) != type([]):
            print("Handling the site event  ")
            print(event)
            beachline, Edges, Q = handle_site(event, beachline, Edges, Q )
            Q.sort(key = lambda cord : cord[1])

        else :
            print("I am going to handle a circle event")
            print(event)
            print('_______________________________________')
            if event == [[[-69, -96], [-77, -99], [84, -88]], -99]:
                pass
            beachline, Edges, Q = handle_circle(event, beachline, Edges, Q)
    return Edges






def handle_site(event, beachline, Edges, Q, check = False):
    """we assume the beachline is not empty since we handled an event
    INPUT: event = [xj, yj]
           beachline as in the preamble
    Summary: 
        - Find the arc above the event
        -- Deal with the special case, if any
        - If it was labeled with a circle event, set it as a False alarm
        - Compute the vertical intersection where the new two edges will start
        - Creat two entries for the new edges with apporpiate index
        - Check for circle_event where the event is the right-most or leftmost
          arc.
        
    """
    # TODO maintain a list of intersection points that have the same length as
    # find the position of the arc that lies above the event
    arc_above  = search_vertical(beachline, event)
    
    # Special case
    if len(arc_above) == 2: #when the new sites intersects two arcs i.e. breakpoint
        i = arc_above[0]
        p1, p2 = beachline[i][0], beachline[i+1][0]
        #choice for a solution of the parabolas intersection
        # x, y of the intersection
        x, position = event[0], vertical_intersection(p1, event)
        
        edg_ind = search_edge(Edges, position)
                      #= [ [p1, p2]        , [Edges[edg_ind][1][0], end       ]                                  ]
        Edges[edg_ind] = [Edges[edg_ind][0], [[Edges[edg_ind][1][0],\
                         (event[0], position)], True ]]
        Edges.insert(edg_ind,  [[event, p2],[(x, position), None]], False )#right
        Edges.insert(edg_ind,  [[p1, event],[(x, position), None]], False )#left
        beachline.insert(i+1, [event, False])
        #Exits
        return beachline, Edges, Q
    
    # Back to the generic case
    # renaming variables for readability
    ind = arc_above[0] #search_vertical alway returns a list of positions
    arc_above = beachline[ind] # = [ [x_p, y_p], boolean]

    #-----------this part is mainly for checking purposes--------------------
    # 
    print("search vertical found: ", tuple(arc_above[0]))
    print("\n ---------------------------------")   
    print("event is ", event)
#    print("beachline is ", beach_cleaned)
#    print("\n--------------------------\n")
#    print("Edges are ", Edges)
#    print("____________________________________________\n\n\n")
    
    #--------End check--------------------------------

    
    # Is there a false alarm?
    if arc_above[-1] != False: arc_above[-1] = False
    # No needs to maintain the circle_event flag
    arc_above = arc_above[0] # = [x_p, y_p]
    
    #x-coordinate of the vertical intersection
    position = vertical_intersection(arc_above, event)
  
    #--- Edges are sorted, hence we look for a suitable index ------
    edg_ind = search_edge(Edges, position)
    if edg_ind: pass #Edges are not an empty list
    else: edg_ind = 0
    #-----------------------
    
    #site = Edges[edg_ind][0][0] #the focal of the arc that has been broken 
    x = event[0]
    Edges.insert(edg_ind,  [[event, arc_above],[(x, position), None]] )
    Edges.insert(edg_ind,  [[arc_above, event],[(x, position), None]] )
    
    #Add two arcs to the beach line
    # Index:     i         i,i+1,i+2
    #          \old/  to   \o/\n/\o/ , o: old, n: new
    #           ---         -  -  -
    beachline.insert(ind+1, [event, False])
    beachline.insert(ind+2, [arc_above, False]) #arc_above ::= [focal, false]
    
    # ---- Checking for circle events -----
    c = False # default value
    if len(beachline[ind:]) >= 4: # do we have enough arcs for a circle event
        m, r, y0  =  beachline[ind+2][0],beachline[ind+3][0], event[1]
        c = check_circle_event(event, m, r, y0)
    
    # a circle event has been detected
    if c:
        print("Circle event has been detected : left")
        beachline[ind+2][1] = True
        #event_to_add = beachline[ind+2][0][:] #deepcopy
        Q.append([[event, m, r], c]) 
        print([[event, m, r], c])
    
    #chekc whe event is the right most
    if len(beachline[:ind]) >= 2: # do we have enough arcs for a circle event
        r, m, y0  =  beachline[ind-1][0], beachline[ind][0], event[1]
        c = check_circle_event(r, m, event, y0)

    if c:
        print("Circle event has been detected: right")
        
        beachline[ind][1] = True
        l, m, r =beachline[ind-1][0] , beachline[ind][0], beachline[ind+1][0]
        print(l, m, r, c)
        Q.append([[l, m, r], c]) 

    print("Beachline is ")
    print(beachline)
    print("--------------------------\n")
    
    return beachline, Edges, Q


def circle_even_init(l, m, r, y,  Q):
    """INPUT left, middle, right are focals of parabolas
    i.e. left = p_k = [xk, yk]
    Q is the Queue event. Sorting is local so we need to preform it outside"""

    c = check_circle_event(l, m, r, y)
    if c: #python treats numbers as true
        Q.append([[l, m, r], y])
    
    return c

def collinear(p1, p2, p3):
    try:
        if p1 == p2 or p2 == p3 or p3 == p1: return True
        return p1[0]/p1[1] == p2[0]/p2[1] == p3[0]/p3[1]  
    except: 
        return p1[1] == p2[1] == p3[1] == 0

def event_finder(event1, event2, Q): 
    for i in range(len(Q)):
        if type(Q[i][0]) == type([]):
            if ( Q[i][0][:2] == [event1, event2] or Q[i][0][1:] == [event1, event2]):
                return i
    
def handle_circle(event, beachline, Edges, Q):
    # event := [[left, middle, right], middle.y] 
    left, middle, right = event[0] # TODO why event passed as tuples?
    y = event[1] #the sweepline position
    #Search for the exact index where the triple occurs    
    ind = search_beach(beachline, left, middle, right) + 1
        
    
    # set the circle event for the two neighboring arcs to false
    # remove them from the queue
    if beachline[ind-1][1]:
        beachline[ind-1][1] = False
        i = event_finder(beachline[ind-1][0], beachline[ind][0], Q)
        del Q[i]
        
    if beachline[ind+1][1]:
        beachline[ind+1][1] = False
        i = event_finder(beachline[ind][0],  beachline[ind+1][0], Q)
        del Q[i]

        
        
    #Where the arc will vanish
    c = circumcenter(left, middle, right)

    #find the corresponding edge
    ind_edg1 = search_beach(Edges, [left, middle])
    ind_edg2 = search_beach(Edges, [middle, right])
    if not ind_edg1 or not ind_edg2: return  beachline, Edges, Q # TODO something wrong!

    
    # Set end points for the edges between left and middle, middle and right      
    # left_edge, right_edge = Edges[ind_edge], Edges[ind_edge+1]
    Edges[ind_edg1][1][1], Edges[ind_edg2][1][1] = c, c
    # Also, They are complete
    Edges[ind_edg1][-1], Edges[ind_edg2][-1] = True, True
    # check for a circle event finally
    #fix the indices
    
    
    try: # we may not always have enough number of edges
        # TODO the code here is not complete!
        left, right = beachline[ind-1], beachline[ind+1]
        left_left, right_right = beachline[ind-2], beachline[ind+2]
        circle_even_init(left_left[0], left[0], right[0], y,  Q)
        circle_even_init(left[0], right[0], right_right[0], y,  Q)
    except: pass
    # Finally, we remove the arc
    del beachline[ind]
    print("Beachline after removing an arc:")
    print(beachline)
    return beachline, Edges, Q

dis = lambda x, y: sqrt( (x[0]-y[0])**2 +  (x[1]-y[1])**2)

def find_first(s, lis):
    """a typical element in lis is in the form [a, ....]
       returns the index of the  first occurence of the
       form [s, ...]"""
    
    for i in range(len(lis)):
        if s == lis[i][0]: return i
       

def search_beach(M, *args):
    """ let args = a1, a2, a3, ...
        returns i where lis[i: len(args)] == a1, a2, a3, ...
        aj := [aj1, aj2, ...]"""
        
    lis = [arg for arg in args]
    if type(lis[0]) != type([]): lis = [lis]
    n = len(lis)
    for i in range(len(M) - n):
        M_mod = [m[0] for m in M[i:i+n]]
        if M_mod == lis: 
            return i

    
if __name__ == '__main__':
    #test sties
    sites = [[-23, -15], [-10, -12], [-27, -69], [-69, -96], [74, 44], [84, -88], [95, 85], [-77, -42], [17, -65], [35, 12], [62, -8], [59, -85], [-17, 76], [-78, -55], [34, -68], [97, 55], [34, 95], [-98, -51], [-5, 57], [62, -50], [-77, -99], [3, -2], [-81, -18], [-49, 77], [56, 26], [61, -42], [-56, 35], [19, 57], [18, 4], [-81, 83]]

    #seg = vor_diag(sites)
    # generate random points
    #from random import randint
    #sites = [[randint(-100, 100), randint(-100, 100)] for i in range(30)]
    #sites = [[-15, -23], [-12, -10], [-69, -27], [-96, -69], [44, 74], [-88, 84], [85, 95], [-42, -77], [-65, 17], [12, 35], [-8, 62], [-85, 59], [76, -17], [-55, -78], [-68, 34], [55, 97], [95, 34], [-51, -98], [57, -5], [-50, 62], [-99, -77], [-2, 3], [-18, -81], [77, -49], [26, 56], [-42, 61], [35, -56], [57, 19], [4, 18], [83, -81]]
    #sites = [ (0, -120), (1, -110), (-12.212670403551893, -100), (-77, -99), (-69, -96), (84, -88), (59, -85), [-27, -69]]    #print(sites)
    #sites = [[s[1], s[0]] for s in sites]
    #print("------------------------------- \n sites reversed \n")
    #print(sites)
    #print("----------------------------")
    seg = vor_diag(sites)
    p1, p2 = (0, -120), (1, -110)
    p3 = (-12.212670403551893, -100)