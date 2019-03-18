#!/usr/bin/env python3
# -*- coding: utf-8 -*-

""" Doubly Connected Edge List
    all points here are assumed to be 2-dimensional"""

class Vertex :
    
    def __init__( self, v, incidentEdge = None):
        self.v = v
        self.x, self.y = v[0], v[1]
        self.incidentEdge = incidentEdge
    
    def v(self):
        return self.v

    #printing 
    def __repr__(self):
        return str(self.v)


class halfEdge :
    
    def __init__(self, origin = None, end = None,  twin = None,\
                 incidentFace = None, next = None, previous = None):
        """While running Fortune's we only add origin and the end. 
        Also, we get information about the incident face since a half-edge 
        seperates two sites."""
    