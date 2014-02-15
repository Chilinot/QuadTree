(*
    Home Assignment 2
    Authors: Lucas Arnström & Gustav Dyrssen
*)

(*
    REPRESENTATION CONVENTION: 
        Rect(left, top, right, bottom):
            Represents a rectangle where each parameter determines the x- or y-coordinate for the edges of the rectangle:
                left   = X-coordinate for the left edge.
                top    = Y-coordinate for the top edge.
                right  = X-coordinate for the right edge.
                bottom = Y-coordinate for the bottom edge.
                
    REPRESENTATION INVARIANT: 
        left < right and bottom < top
*)
datatype rectangle = Rect of int * int * int * int;

(*
    REPRESENTATION CONVENTION: 
        Qt(extent, horizontal, vertical, northWest, northEast, southWest, southEast):
            Represents a quadTree where each parameter represents:
                extent     = A rectangle that determines the region covered by the quadTree.
                horizontal = A list of rectangles that contain some point along the horizontal centre line.
                vertical   = A list of rectangles that contain some point along the vertical centre line.
                northWest  = A sub-quadTree in the top left quadrant of this quadTree.
                northEast  = A sub-quadTree in the top right quadrant of this quadTree.
                southWest  = A sub-quadTree in the bottom left quadrant of this quadTree.
                southEast  = A sub-quadTree in the bottom right quadrant of this quadTree.
                
        EmptyQuadTree:
            Represents an empty quadTree.
         
        REPRESENTATION INVARIANT: 
            True.
*)
datatype quadTree = EmptyQuadTree | Qt of rectangle * rectangle list * rectangle list * quadTree * quadTree * quadTree * quadTree;

(*
    emptyQtree e
    TYPE:    rectangle -> quadTree
    PRE:     True
    POST:    Empty quadTree with extent e.
    EXAMPLE: emptyQtree(Rect(1,5,3,2)) = (Rect (1, 5, 3, 2), [], [], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree)
    
    TIME COMPLEXITY: O(1)
*)
fun emptyQtree(e) = Qt(e, [], [], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree);

(*
    newIfEmpty(tree, r)
    TYPE:    quadTree * rectangle -> quadTree
    PRE:     True
    POST:    A new quadTree if tree parameter is equal to EmptyQuadTree with the extent r, otherwise it returns the tree parameter.
    EXAMPLE: 
        newIfEmpty(Qt(Rect (0, 100, 100, 0), [], [Rect (0, 50, 50, 0)], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree), Rect(0,100,100,0)) = Qt(Rect (0, 100, 100, 0), [], [Rect (0, 50, 50, 0)], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree)
        newIfEmpty(EmptyQuadTree, Rect(0,100,100,0)) = Qt(Rect (0, 100, 100, 0), [], [], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree)
    
    TIME COMPLEXITY: O(1)
*)
fun newIfEmpty(EmptyQuadTree, r) = emptyQtree(r)
|   newIfEmpty(quadtree, _)      = quadtree;

(*
    insert(tree, rectangle)
    TYPE:         quadTree * rectangle -> quadTree
    PRE:          tree is not an instance of quadTree equal to EmptyQuadTree, and rectangle can fit inside the extent of the given tree.
    POST:         quadTree based on tree, containing the given rectangle.
    SIDE EFFECTS: Exception if tree is EmptyQuadTree or rectangle does not fit within the extent of tree.
    EXAMPLE:      insert(emptyQtree(Rect(0,100,100,0)), Rect(0,50,50,0)) = Qt(Rect (0, 100, 100, 0), [], [Rect (0, 50, 50, 0)], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree)
    VARIANT:      Extent of the tree.
    
    TIME COMPLEXITY: O(log n)
*)
fun insert(EmptyQuadTree, r) = raise Fail "Can not work with an instance of quadTree equal to EmptyQuadTree!"
|   insert(Qt(e as (Rect(eLeft,eTop,eRight,eBottom)), hList, vList, nw, ne, sw, se), r as (Rect(rLeft, rTop, rRight, rBottom))) = 
    let
        val centVert = (eLeft +  eRight)  div 2
        val centHori = (eTop  +  eBottom) div 2
        val north    = rTop   >  centHori
        val west     = rLeft  <= centVert
    in
        if eLeft <= rLeft andalso eTop >= rTop andalso eRight >= rRight andalso eBottom <= rBottom then
            (* LIST - VERTICAL *)
            if rLeft <= centVert andalso rRight > centVert then
                Qt(e, hList, r :: vList, nw, ne, sw, se)
            
            (* LIST - HORIZONTAL *)
            else if rTop > centHori andalso rBottom <= centHori then
                Qt(e, r :: hList, vList, nw, ne, sw, se)
            
            (* QUADRANT - NORTH WEST *)
            else if north andalso west then
                Qt(e,hList,vList,insert(newIfEmpty(nw,Rect(eLeft,eTop,centVert,centHori)),r),ne,sw,se)     
            
            (* QUADRANT - NORTH EAST *)
            else if north andalso not west then
                Qt(e,hList,vList,nw,insert(newIfEmpty(ne,Rect(centVert,eTop,eRight,centHori)),r),sw,se)    
            
            (* QUADRANT - SOUTH WEST *)
            else if not north andalso west then
                Qt(e,hList,vList,nw,ne,insert(newIfEmpty(sw,Rect(eLeft,centHori,centVert,eBottom)),r),se)  
            
            (* QUADRANT - SOUTH EAST *)
            else
                Qt(e,hList,vList,nw,ne,sw,insert(newIfEmpty(se,Rect(centVert,centHori,eRight,eBottom)),r)) 
        else
            raise Fail "The given rectangle does not fit inside the given quadtree!"
    end;

(*
    retrieveRects(list, x, y)
    TYPE:    rectangle list * int * int -> rectangle list
    PRE:     True
    POST:    List of rectangles in list-parameter containing the point defined by parameters x and y.
    EXAMPLE: retrieveRects([Rect(0,20,20,0), Rect(10,90,10,60)], 10, 10) = [Rect(0,20,20,0)]
    VARIANT: Length of list.
    
    TIME COMPLEXITY: O(n)
*)
fun retrieveRects([],_,_) = []
|   retrieveRects((head as (Rect(l,t,r,b)))::list,x,y) = 
    if x >= l andalso x <= r andalso t >= y andalso b <= y then
        head :: retrieveRects(list,x,y)
    else
        retrieveRects(list,x,y);
        
(*
    retrieveQuadrant(tree, x, y)
    TYPE:    quadTree * int * int -> quadTree
    PRE:     x and y defines a point inside the given tree.
    POST:    Quadrant with the extent that covers the point defined by x and y. EmptyQuadTree if x and/or y can be found on horizontal and/or vertical centre line.
    EXAMPLE: retrieveQuadrant(Qt(Rect (0, 100, 100, 0), [], [], Qt(Rect (0, 100, 50, 50), [], [], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree), EmptyQuadTree, EmptyQuadTree, EmptyQuadTree), 20,90) = Qt(Rect (0, 100, 50, 50), [], [], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree)
    
    TIME COMPLEXITY: O(1)
*)         
fun retrieveQuadrant(EmptyQuadTree,_,_) = EmptyQuadTree
|   retrieveQuadrant(Qt(Rect(l, t, r, b),_,_, northWest, northEast, southWest, southEast), x, y) = 
    let
        val horizontal = (t+b) div 2
        val vertical   = (l+r) div 2
    in
        if x = vertical orelse y = horizontal then
            EmptyQuadTree
        else if x < vertical andalso y > horizontal then
            northWest
        else if x > vertical andalso y > horizontal then
            northEast
        else if x < vertical andalso y < horizontal then
            southWest
        else
            southEast
    end;
                
(*
    query(tree, x, y)
    TYPE:         quadTree * int * int -> rectangle list
    PRE:          X and Y defines a point inside the extent of the given tree.
    POST:         A list of rectangles that all contains the point defined by x and y.
    SIDE EFFECTS: Raises an exception if the point defined by x and y can not be located within the extent of the tree.
    EXAMPLE:      query(Qt(Rect (0, 100, 100, 0), [], [Rect (0, 50, 50, 0)], EmptyQuadTree, EmptyQuadTree, EmptyQuadTree, EmptyQuadTree), 10,10) = [Rect(0,50,50,0)]
    VARIANT:      Depth of the tree.
    
    TIME COMPLEXITY: O(log n)
*) 
fun query(EmptyQuadTree,_,_) = []
|   query(tree as (Qt(Rect(l,t,r,b), horizontalList, verticalList, _, _, _, _)), x, y) = 
    if x <= r andalso x >= l andalso y >= b andalso y <= t then
        retrieveRects(horizontalList @ verticalList, x, y) @ query(retrieveQuadrant(tree, x, y), x, y)
    else
        raise Fail "The given point can not be located within the extent of the given tree!";
        
        
        