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
---- circle_event = [[l, m, r], y] the three arcs with the y-coordinate when
                     m vanish

- Edges
- Edges = [ [(p_k, p_l), [start, end] , boolean], ...]
-- (pj_k, p{j+1}_l) the two sites that are seperated by the edge.
-- end can be None untill it is discovered by a circle event.
-- boolean indicates it's a complete edge. This feature is for drawing.
- edges = [(start, end), ...] we may add the sites that they seperate.

- Queue:
- Q = [site_event, or circle_event] ordered by y-coordinate of the focal point
-- site_event = pj = [xj, yj]
-- circle_event = circumcenter | False

- Sweeplines
-- if event = [[x0,y0], ...], or [x0, y0] then the sweepline is y = y0

- Parabolas:
    The parabolas p whith focal (x1, y1) and directrix y0 has the equation:
                ((x-x1)**2 + y1**2 - y0**2) / 2*(y1-y0)

- Features to add:
-- Plotting
-- Add test results for each function

"""

from math import sqrt

#                      Auxiliaries Functions

###############################################################################
#------------------------Searching Lists--------------------------------------# 
def find_first(s, lis):
    """a typical element in lis is in the form [a, ....]
       returns the index of the  first occurence of the
       form [s, ...]"""
    
    for i in range(len(lis)):
        if s == lis[i][0]: return i
       

def search_beach(M, *args): # TODO find a better name
    """ let args = a1, a2, a3, ...
        returns i where lis[i: len(args)] == a1, a2, a3, ...
        aj := [aj1, aj2, ...]"""
        
    lis = [arg for arg in args]
    if type(lis[0]) != type([]): lis = [lis]
    n = len(lis)
    m = len(M) - n+1
#    print("I am doing a search: ", m)
    for i in range(m):
        M_mod = [m[0] for m in M[i:i+n]]
        if M_mod == lis: 
            return i

def event_finder(event1, event2, Q): 
    for i in range(len(Q)):
        if type(Q[i][0]) == type([]):
            if ( Q[i][0][:2] == [event1, event2] or Q[i][0][1:] == [event1, event2]):
                return i

def event_finder2(e1, e2, e3, Q):
    for i in range(len(Q)):
        if type(Q[i][0]) == type([]) and Q[i][0] == [e1, e2, e3] :
                return i

#-----------------------------------------------------------------------------#
###############################################################################
            
###############################################################################
#------------------------Geometric Functions----------------------------------#

def parabola (p, y0):
    """
    p is the focal, y0 is the directrix"""
    
    x1, y1 = p
    return lambda x: ((x-x1)**2 + y1**2 - y0**2) / 2*(y1-y0)


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
    # A special case when py1 = py2
    if py1 == py2: return ((px1+px2)/2, 0, 1)
    
    #y0 is the horizontal directrix
    a = (px2*py1 - px1*py2 + (px1 - px2)*y0)
    b = (py1 - py2)
    disc = -2*py1**2*py2**2 + py1*py2**3 + (px1**2 - 2*px1*px2 + px2**2 + py1**2 - 2*py1*py2 + py2**2)*y0**2 + (py1**3 + (px1**2 - 2*px1*px2 + px2**2)*py1)*py2 - (py1**3 - py1*py2**2 + py2**3 + (px1**2 - 2*px1*px2 + px2**2)*py1 + (px1**2 - 2*px1*px2 + px2**2 - py1**2)*py2)*y0
    return (a, disc, b)

def before(p1, p2, p):
    """ Check: not ok!
    two case:
    break  |      
        p1 | p2   
        \_/*\_/    
         ^             
         |        
         p        
    is p before the point "*" ? Does p lie on the same vertical level as "*"?
    OUTPUT: [i, flag]   
            * i := False when p is on the right of *
            * i := True when p is on the left  of * 
            * flag :=  True when p is exactly on the same vertical line as *
            * flag := False otherwise """
    # (a + sqrt(disc))/ b is a solution of a quadratic formula
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
    
    equality =  abs(star - x_site) < 0.00001 #almost equal    
    if star > x_site:
        return [True, False]
    if equality:
        return [True, True]
    return [False, False]

def search_vertical(beachline, site):
    #TODO: the list is an ordered list, use this fact!
    """  
        INPUT:
        beachline as in the preamble
        site = site_event
       OUTPUT: the index/indices of arc(s) where the vertical line passes through
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
    # TODO a special case when py = y0 i.e. two sites have the same y-coordinate
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

def collinear(p1, p2, p3):
    try:
        if p1 == p2 or p2 == p3 or p3 == p1: return True
        return p1[0]/p1[1] == p2[0]/p2[1] == p3[0]/p3[1]  
    except: 
        return p1[1] == p2[1] == p3[1] == 0


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

#-----------------------------------------------------------------------------#
###############################################################################



#---------------- Fucnctions that act on beachline and Q ---------------------#

def check_circle_event( ind, y0, beachline, Q):
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
    
    if ind == 0 or ind == len(beachline) -1 : 
        return  beachline, Q # no possible circle event
    l, m, r = beachline[ind-1][0], beachline[ind][0], beachline[ind+1][0] 
    
    if collinear(l, m, r): 
        return  beachline, Q # no possible circle event

    lx, ly = l
    mx, my = m
    rx, ry = r    
    # check if bc is a "right turn" from
    # Details?!
    if ((my - ly)*(rx - lx) - (ry - ly)*(mx - lx)) > 0: 
        return  beachline, Q # no possible circle event

    c = circumcenter(l, m, r) 

    radius   = sqrt((c[0] - m[0])**2   + (c[1] - m[1])**2)
    upper_point = [c[0], radius+c[1]]
    
    if upper_point[1] < y0: 
        return  beachline, Q # no possible circle event
    
    beachline[ind][1] = True
    #event_to_add = beachline[ind][0][:] #deepcopy
    Q.append([[l, m, r], upper_point[1]]) 
    return  beachline, Q # circle event



    

def false_alarm(ind, beachline, Q):
    """ if beachline[ind] has a circle event, remove it from Q and set it to 
        false.
        INPUT: As in the preamble
        """
    # If it is already indicated as False
    if not beachline[ind][1]: return beachline, Q
    
    # set the circle event for the two neighboring arcs to false
    # remove them from the queue
    beachline[ind][1] = False
    i = event_finder2(beachline[ind-1][0], beachline[ind][0], beachline[ind+1][0], Q)
    del Q[i]
    return beachline, Q

#-----------------------------------------------------------------------------#


def voronoi_diagram(sites):
    #initialize
    #Q, beachline, voronoi
    Q, beachline, Edges = sites, [], []
    #sort Q according to the y-coordinate
    Q.sort(key = lambda cord : cord[1])

    beachline = [[Q.pop(0), False]] #no circle event yet

    while Q: #not empty
        event = Q.pop(0) #Q = [a, b, c] --> event = a ,   Q = [b, c]

        if type(event[0]) != type([]):
            beachline, Edges, Q = handle_site(event, beachline, Edges, Q )
            Q.sort(key = lambda cord : cord[1])

        else :
            beachline, Edges, Q = handle_circle(event, beachline, Edges, Q)
            Q.sort(key = lambda cord : cord[1])
            
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
    arc_above  = search_vertical(beachline, event)
    
    # Special case
    if len(arc_above) == 2: #when the new sites intersects two arcs i.e. breakpoint
        i = arc_above[0]
        p1, p2 = beachline[i][0], beachline[i+1][0]
        #choice for a solution of the parabolas intersection
        # x, y of the intersection
        x, position = event[0], vertical_intersection(p1, event)
        

        edg_ind = search_beach(Edges, [p1, p2])        
              #= [ [p1, p2]        , [Edges[edg_ind][1][0], end       ]                                  ]
        Edges[edg_ind] = [Edges[edg_ind][0], [[Edges[edg_ind][1][0],\
                         (event[0], position)], True ]]
        Edges.append([[event, p2],[(x, position), None]] )#right
        Edges.append([[p1, event],[(x, position), None]] )#left
        beachline.insert(i+1, [event, False])
        #Exits
        return beachline, Edges, Q
    
    # Back to the generic case
    # renaming variables for readability
    ind = arc_above[0] #search_vertical alway returns a list of positions
    arc_above = beachline[ind] # = [ [x_p, y_p], boolean]
    arc_above = arc_above[0] # = [x_p, y_p]


    
    # Does arc_above has a circle? If so, remove it.
    beachline, Q = false_alarm(ind, beachline, Q)
    
    #x-coordinate of the vertical intersection
    position = vertical_intersection(arc_above, event)
  
    #--- Edges are NOT sorted, hence we look for a suitable index ------    
    x = event[0]
    Edges.append( [[event, arc_above],[(x, position), None]] )
    Edges.append([[arc_above, event],[(x, position), None]] )
    
    #Add two arcs to the beach line
    # Index:     i         i,i+1,i+2
    #          \old/  to   \o/\n/\o/ , o: old, n: new
    #           ---         -  -  -
    beachline.insert(ind+1, [event, False])
    beachline.insert(ind+2, [arc_above, False]) #arc_above ::= [focal, false]
    
    # ---- Checking for circle events -----
    # Check only the cases when the new site is either leftmost or rightmost
    y0 = event[1] #the current position of the sweepline
    beachline, Q = check_circle_event(ind+2, y0, beachline, Q)
    beachline, Q = check_circle_event(ind, y0, beachline, Q)
    
    return beachline, Edges, Q

    
def handle_circle(event, beachline, Edges, Q):
    """ 
    INPUT: 
        event = [[left, middle, right], y]
        left, middle, right are consecutive arcs in the beachline
        y indicates the position of the sweep line and where middle will 
        disappear. 
        
    OUTPUT: beachline, Edges, Q
    Summary:
        - unpack the elements and find 'middle' position in the beachline
        - Check if left or right has a circle event. If so, change it to False
          and remove it from Q.
        - Add end points for the edges between left, middle and middle, right
        - Add a new edge which starts add at the end point of left, middle and 
          middle, right
        - Finally, check for circle events for left left, left, right and  
          left, right, right right.
    """
    
    
    left, middle, right = event[0] 
    y = event[1] # the sweepline position
    #Search for the exact index where the triple occurs    
    ind = search_beach(beachline, left, middle, right) + 1

    # If a neighbouring arc has a circle event then it's a false alarm.
    beachline, Q = false_alarm(ind-1, beachline, Q)
    beachline, Q = false_alarm(ind+1, beachline, Q)

        
    #Add a new edge # TODO check 
#    p_l, p_r = beachline[ind-1][0], beachline[ind+1][0]
#    a, b, disc = parabolas_intersection(p_l, p_r, y)    
#    s_x = (a+sqrt(disc))/b
#    s_y = (parabola(p_l,y))(s_x) 
    c = circumcenter(left, middle, right)
    Edges.append([[left, right], [c, None]])        
        

    # find the corresponding edge
    ind_edg1 = search_beach(Edges, [left, middle])
    ind_edg2 = search_beach(Edges, [middle, right])

    
    # Set end points for the edges between left and middle, middle and right      
    # left_edge, right_edge = Edges[ind_edge], Edges[ind_edge+1]
    Edges[ind_edg1][1][1], Edges[ind_edg2][1][1] = c, c
    # Also, They are complete
    Edges[ind_edg1].append(True), Edges[ind_edg2].append(True)

    # indices: ind-2     (ind-1)  ind   ind+1    ind+2
    #        (left left)  left   event  right (right right)
    # (left left) and (right right ) may not exist.
    del beachline[ind]


    # Finally, check if there is a circle event after the removal
    # After deletion:    
    i_left, i_right = ind-1, ind
    beachline, Q = check_circle_event(i_left, y, beachline, Q)
    beachline, Q = check_circle_event(i_right, y, beachline, Q)

    return beachline, Edges, Q


    
if __name__ == '__main__':
    #test sties
    #from random import randint
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
    segments = voronoi_diagram(sites)
    
    #storing the line segments in a file called edges
    complete_edges = [edge[1] for edge in segments if edge[-1] == True ]
    with open("edges", 'w') as edges:
        for e in complete_edges:
            string = str(e[0][0]) + " " + str(e[0][1]) + " moveto "\
                    + str(e[1][0]) + " " + str(e[1][1])
            edges.write(string+" lineto\n")
