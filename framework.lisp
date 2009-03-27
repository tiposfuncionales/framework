;;; Thu Mar 18 23:32:43 1993 by Mark Kantrowitz <mkant@GLINDA.OZ.CS.CMU.EDU>
;;; framework.lisp -- 131661 bytes

;;; ****************************************************************
;;; FrameWork: A Frame Knowledge Representation Language ***********
;;; ****************************************************************
;;;
;;; FrameWork is a common-lisp portable frame-based knowledge 
;;; representation language. It combines some of the better features
;;; of a variety of other frame languages. It includes a variety of
;;; tools for building, examining, and using knowledge-based systems.
;;; It is intended primarily to be a solid example of how such a system
;;; could be built. FrameWork is easily extended.
;;;
;;; Features: 
;;;    Generic demons (active values) & procedural attachment.
;;;    Object-Oriented Programming with attribute and behavior inheritance 
;;;    in an associative network (methods and message passing)
;;;    Cached values, Default values, Listener,
;;;    Object database maintenance utilities.
;;;
;;; See associated file frame-systems.text for a listing of a variety
;;; of other frame systems. 
;;;
;;; The FRL Manual and the FrameKit (v2.0) User's Guide were read to 
;;; ensure that this system did not overlook any of the basic 
;;; functionality of frame systems. The MacPIKS (v1.0) User's Guide
;;; (a frame system implemented by the author for the Planning Research
;;; Corporation in 1985) was also read to verify that FrameWork
;;; did *not* accidentally include any innovative ideas developed for 
;;; MacPIKS. 
;;;
;;; Written by Mark Kantrowitz, December 1990.
;;; Address:   School of Computer Science
;;;            Carnegie Mellon University
;;;            Pittsburgh, PA 15213
;;; 
;;; Copyright (c) 1990-1993. All rights reserved.
;;; 
;;; See general license below.
;;;

;;; ****************************************************************
;;; General License Agreement and Lack of Warranty *****************
;;; ****************************************************************
;;;
;;; This software is distributed in the hope that it will be useful (both
;;; in and of itself and as an example of lisp programming), but WITHOUT
;;; ANY WARRANTY. The author(s) do not accept responsibility to anyone for
;;; the consequences of using it or for whether it serves any particular
;;; purpose or works at all. No warranty is made about the software or its
;;; performance. 
;;; 
;;; Use and copying of this software and the preparation of derivative
;;; works based on this software are permitted, so long as the following
;;; conditions are met:
;;; 	o  The copyright notice and this entire notice are included intact
;;; 	   and prominently carried on all copies and supporting documentation.
;;; 	o  No fees or compensation are charged for use, copies, or
;;; 	   access to this software. You may charge a nominal
;;; 	   distribution fee for the physical act of transferring a
;;; 	   copy, but you may not charge for the program itself. 
;;; 	o  If you modify this software, you must cause the modified
;;; 	   file(s) to carry prominent notices (a Change Log)
;;; 	   describing the changes, who made the changes, and the date
;;; 	   of those changes.
;;; 	o  Any work distributed or published that in whole or in part
;;; 	   contains or is a derivative of this software or any part 
;;; 	   thereof is subject to the terms of this agreement. The 
;;; 	   aggregation of another unrelated program with this software
;;; 	   or its derivative on a volume of storage or distribution
;;; 	   medium does not bring the other program under the scope
;;; 	   of these terms.
;;; 	o  Permission is granted to manufacturers and distributors of
;;; 	   lisp compilers and interpreters to include this software
;;; 	   with their distribution. 
;;; 
;;; This software is made available AS IS, and is distributed without 
;;; warranty of any kind, either expressed or implied.
;;; 
;;; In no event will the author(s) or their institutions be liable to you
;;; for damages, including lost profits, lost monies, or other special,
;;; incidental or consequential damages arising out of or in connection
;;; with the use or inability to use (including but not limited to loss of
;;; data or data being rendered inaccurate or losses sustained by third
;;; parties or a failure of the program to operate as documented) the 
;;; program, even if you have been advised of the possibility of such
;;; damanges, or for any claim by any other party, whether in an action of
;;; contract, negligence, or other tortious action.
;;; 
;;; The current version of this software may be obtained by anonymous 
;;; ftp from 
;;;    ftp.cs.cmu.edu:/user/ai/areas/kr/frames/framewrk/ [128.2.206.173]
;;; 
;;; Please send bug reports, comments, questions and suggestions to
;;; mkant@cs.cmu.edu. We would also appreciate receiving any changes
;;; or improvements you may make. 
;;; 
;;; If you wish to be added to the Lisp-Utilities@cs.cmu.edu mailing list, 
;;; send email to Lisp-Utilities-Request@cs.cmu.edu with your name, email
;;; address, and affiliation. This mailing list is primarily for
;;; notification about major updates, bug fixes, and additions to the lisp
;;; utilities collection. The mailing list is intended to have low traffic.
;;;

;;; ********************************
;;; Change Log *********************
;;; ********************************
;;;
;;;  mk   = Mark Kantrowitz <mkant@cs.cmu.edu>
;;;  nick = Nick Afshartous <nick@dmi.stevens-tech.edu> or <afshar@cs.nyu.edu>
;;;
;;;  18-NOV-90  mk   File created.
;;;  12-DEC-90  mk   First released version.
;;;   7-DEC-92  nick Changed some of the framework symbols to keywords
;;;                  so the stuff in this file could be placed in its own
;;;                  package. Verified demons and methods.
;;;                  Changed DEFCLASS to take slots as an &rest arg.
;;;                  Made instances inherit demons.
;;; 26-FEB-93 mk    Verified and extended some of Nick's changes.
;;;                 Changed several symbols to keywords that Nick missed.
;;;                 Fixed package definition to be CLtL2 compliant.
;;; 15-MAR-93 mk    Fixed problem with frameget-z caused by :value being both a
;;;                 facet and a demon.
;;; 18-MAR-93 mk    Modified the $ and $! reader macros to rebind the readtable
;;;                 instead of modifying and restoring the Common Lisp
;;;                 readtable. For some reason, AKCL barfs on this.

;;; ********************************
;;; To Do **************************
;;; ********************************
;;;
;;; Verify & Test:
;;;    demons, methods, defclass, make-instance, frameget-Z, heritage.
;;;    set of test frames, test demons and methods.
;;;
;;; Attach comments to data (frame) saying who and when modified. 
;;;
;;; Frame Tracing Facility:
;;;    ftrace, funtrace.
;;; Traces before and after a given facet is executed. Can specify
;;; when something should be printed, when it should call break
;;; to go into the debugger, and what it should print.   
;;;     print traces (*fw-trace*), print warnings (*fw-verbose*)
;;;
;;; Add RESTICTIONS (require facet of FRL):
;;;    serves as constraints on the values that may fill the
;;;    value facet. These are predicates on the VALUE which may
;;;    fill the :value facet. When frameput tries to add a
;;;    value, if a restriction demon returns nil, it fails and
;;;    prints an error message (if *fw-verbose* is t). The
;;;    predicates take VALUE and VALUES as args. 
;;;
;;; Follow framekit idea of abstract data types for frames?
;;; i.e., have all lowlevel functions which deal with the structure
;;; of the representation actually be macros and isolate them from
;;; the rest of the code. 
;;;
;;; Random to do comments are sprinkled throughout the code.
;;;


;;; ****************************************************************
;;; Documentation **************************************************
;;; ****************************************************************
;;;
;;; FrameWork, like all other frame based systems, is ultimately based
;;; on Minsky's frame theory of the representation of knowledge [Minsky 1975].
;;; A frame is an object with an associated list of attributes. Objects
;;; (ala object-oriented programming) are data structures with associated
;;; procedures. The attributes of a frame include VALUES and BEHAVIORS.
;;; Some behaviors, called DEMONS, are functions attached to attributes
;;; to monitor their access and modification, and initiate actions
;;; if invoked or otherwise activated. 
;;;
;;; Using frames we can create a network of objects representing facts,
;;; things, and other concepts, connected through a variety of links.
;;; Objects and their links are represented as frames with names, slots,
;;; facets, and values. (Other frame systems may have more levels of
;;; representation. The primitives given in FrameWork, however, are easily
;;; extended to arbitrary numbers of levels because of the uniformity of
;;; representation.) Each object has a name (frame) and a set of slots;
;;; each slot has a set of facets; and each facet has a set of values.
;;; Values may be arbitrary lisp objects, including functions
;;; and the name of other frames. In some sense a frame is a generalized
;;; property list: it contains more than just values, and can inherit 
;;; information from related frames.
;;;
;;; Frames are implemented as nested association lists (key-value pairs) and
;;; are stored in a hash table under the frame name for efficient access:
;;;       (<frame name>
;;;		 (<slot1> (<facet1> . (<value1> <value2> ...))
;;;			  (<facet2> . (<value1> ...))
;;;			  ...)
;;;		 (<slot2> (<facet1> . (<value1> ...)) ...)
;;;		 ...)
;;;
;;; Slots may be used to name relations by making the name of one frame
;;; the value of the slot in another frame. For example, the :AKO slot
;;; (an abbreviation for "A Kind Of") and its inverse, :KINDSOF, link
;;; objects in the class hierarchy. Many other types of links exist,
;;; including user-defined links. These relations may be used to 
;;; connect the frames into a network. (Note that the relationship defined
;;; by :AKO links is a network and need not be a hierarchy, since it is
;;; permissible for an object to have more than one :AKO value, and for
;;; many objects to be linked to the same parent by :AKO slot. For many
;;; functions even :AKO cycles are permitted, since these functions
;;; specifically check for cycles.)
;;;
;;; The primary facet is :VALUE, which is used to store the value of an
;;; attribute. Other system defined facets include :DEFAULT, :MODE,
;;; :METHOD, :If-Needed, :If-Fetched, :If-Removed. The :MODE facet is used
;;; to associate properties with objects. The :METHOD facet is used to
;;; name procedures that are invoked in response to messages to an object.
;;; The :If-Needed, :If-Fetched, :If-Removed, and :DEFAULT facets are demons 
;;; which are used to monitor the :VALUE facet. 
;;;
;;; In addition, there are demons which monitor the :VALUE facet and maintain
;;; inverse-slot relationships for any values stored there. For example,
;;; whenever a value x is stored into the :AKO slot of the object y, this
;;; demon automatically stores y into the :KINDSOF slot of the object x.
;;;


;;; ********************************
;;; User Guide *********************
;;; ********************************
;;;
;;; *VERSION* ("2.1  MON 15-MAR-93 12:00:47")                       [PARAMETER]
;;;    Current version number/date for FrameWork.
;;;
;;; *DEFAULT-INHERITANCE-LINK* (:ako)                                [VARIABLE]
;;;    Default link used for inheritance in FrameWork.
;;;
;;; *DEFAULT-INHERITANCE-FACET* (:value)                             [VARIABLE]
;;;    Default facet used for inheritance in FrameWork.
;;;
;;; FRAMEWORK-COPYRIGHT (&optional (stream *standard-output*))       [FUNCTION]
;;;    Prints a FrameWork copyright notice and header upon startup.
;;;
;;; CURRENT-TIME-STRING (&optional (mode 'hyphen))                   [FUNCTION]
;;;    Returns a string for the current time and date in a variety of modes.
;;;
;;; DATE-STRING (month date year &optional (mode 'hyphen))           [FUNCTION]
;;;    Given a date, returns a string for the date in a variety of modes.
;;;
;;; YEAR-STRING (year &optional (mode 'long))                        [FUNCTION]
;;;    Formats a year number in various ways.
;;;
;;; TIME-STRING (hour min secs &optional (mode 'full))               [FUNCTION]
;;;    Formats the current time in a variety of ways.
;;;
;;; DOW-STRING (dow &optional (mode 'short))                         [FUNCTION]
;;;    Formats the day of week in a variety of modes.
;;;
;;; MONTH-STRING (month &optional (mode 'short))                     [FUNCTION]
;;;    Formats the month in a variety of ways.
;;;
;;; FRAMEWORK-HERALD (&optional (stream *standard-output*))          [FUNCTION]
;;;    Prints a FrameWork Herald. Does basic copyright statement,
;;;    as well as the time and date.
;;;
;;; EQMEMB (item list &key (test #'equal))                           [FUNCTION]
;;;    Checks whether ITEM is either equal to or a member of LIST.
;;;
;;; NEQ (x y)                                                        [FUNCTION]
;;;    not eq
;;;
;;; CAR-EQ (x y)                                                     [FUNCTION]
;;;    Checks whether Y is eq to the car of X.
;;;
;;; DREMOVE (item list)                                              [FUNCTION]
;;;    Destructive remove which replaces the original list with the list
;;;    that results when ITEM is deleted from LIST.
;;;
;;; DISPLACE (list val)                                              [FUNCTION]
;;;    Replaces LIST with VAL by destructively modifying the car and cdr of
;;;    LIST. Warning: VAL must not share list structure with LIST or you'll
;;;    be sorry. 
;;;
;;; TAILPUSH (item list)                                             [FUNCTION]
;;;    Pushes ITEM onto the tail of LIST. Does not work if the list is null.
;;;
;;; DO-QUEUE (((&optional (node 'node) (queue 'queue)                   [MACRO]
;;;           (children 'children) visited) initial-queue children-form
;;;           &optional (dequeue-form '(pop queue)) (merge-form '
;;;           (setq queue (append queue progeny))) result-form)
;;;           &body body)
;;;    Implements generic search using a queue representation. 
;;;    If the VISITED iteration variable is specified, checks to see if a
;;;    node has already been visited before proceeding, to prevent
;;;    infinite loops in the search when cycles are encountered. It also
;;;    prevents multiple occurrences of a node when several inheritance
;;;    paths lead to the same node. If VISITED is specified, it is the name
;;;    of the variable where the search history is maintained.
;;;
;;; *FRAME-TABLE* ((make-hash-table :test #'equal))                  [VARIABLE]
;;;    Hash table where all the frame definitions are stored. 
;;;    Since we are using a hash table instead of a property list, the
;;;    frame name need not be an atom. This allows us to attach
;;;    information to any lisp object.
;;;
;;; *FRAMES* (nil)                                                   [VARIABLE]
;;;    Global list of the names of all user defined frames.
;;;
;;; *SYSTEM-FRAMES* (nil)                                            [VARIABLE]
;;;    Global list of all system defined frame names. These frames define
;;;    the default relations (slots) and their inverses. Frames included
;;;    on this list are normally invisible to user deleting and saving
;;;    operations.
;;;
;;; DEFINE-FRAME (name frame)                                        [FUNCTION]
;;;    Internal function for creating a new frame. Pushes the name of the 
;;;    frame onto the list of user defined frames.
;;;
;;; CREATE-FRAME (name)                                              [FUNCTION]
;;;    Creates a new blank frame named NAME.
;;;
;;; DEF-FRAME (name frame)                                              [MACRO]
;;;    External function for creating a new frame. The name and
;;;    frame do not need to be quoted.
;;;
;;; FRAME (name)                                                     [FUNCTION]
;;;    Returns the frame "property" (frame structure) of NAME if there is
;;;    one; otherwise returns nil.
;;;
;;; FRAME+ (framename)                                               [FUNCTION]
;;;    Gets the frame associate with framename. If a frame structure does
;;;    not already exist, creates a new one and returns it.
;;;
;;; FRAMEP (name)                                                    [FUNCTION]
;;;    Predicate which returns T if NAME names a defined frame, nil
;;;    otherwise. 
;;;
;;; DELETE-FRAME (frame)                                             [FUNCTION]
;;;    Deletes a frame definition without removing any references 
;;;    to the frame in other frames.
;;;
;;; DELETE-FRAMES (&optional (frame-list *frames*))                  [FUNCTION]
;;;    Deletes a specified list of frames, which defaults to all user
;;;    defined frames. Evaluating (delete-frames) is a quick way to
;;;    undo your work without eliminating the system defined frames.
;;;
;;; FLISTP (flist)                                                   [FUNCTION]
;;;    Returns T if the FLIST is a flist.
;;;
;;; FLIST-KEY (flist)                                                [FUNCTION]
;;;    Returns the key of a flist.
;;;
;;; FLIST-BUCKET (flist)                                             [FUNCTION]
;;;    Returns the bucket of a flist.
;;;
;;; FLIST-KEYS (flist)                                               [FUNCTION]
;;;    Returns a list of the keys of the items in the bucket of flist.
;;;
;;; FRAMEASSOC (key flist &key (test #'eq))                          [FUNCTION]
;;;    Finds the item with key KEY in the FLIST if present.
;;;
;;; FRAMEASSOC+ (key flist &key (test #'eq))                         [FUNCTION]
;;;    Finds item with key KEY in the FLIST if present, otherwise inserts
;;;    it. Returns the entry.
;;;
;;; FLIST-GET (flist &rest path)                                     [FUNCTION]
;;;    Follows the key path down to the value. For retrieving items from
;;;    an flist.
;;;
;;; FLIST-PUT (flist item &rest path)                                [FUNCTION]
;;;    Stores ITEM in the bucket pointed to by the path of keys.
;;;    Returns the modified FLIST.
;;;
;;; FLIST-DELETE (flist &rest path)                                  [FUNCTION]
;;;    Deletes the entire item accessed. Returns the modified FLIST.
;;;
;;; FLIST-CLEAR (flist &rest path)                                   [FUNCTION]
;;;    Deletes the bucket of the indicated item, but leaves the key.
;;;    Returns the modified FLIST.
;;;
;;; FLIST-REPLACE (flist item &rest path)                            [FUNCTION]
;;;    Replaces all existing items with the item. Returns the modified
;;;    FLIST. Equivalent to Flist-Clear followed by Flist-Put.
;;;
;;; FRAMEGET (frame slot &optional (facet :value) (no-demons t))     [FUNCTION]
;;;    Fetches information from a frame given an access path consisting of
;;;    a frame, a slot, and a facet. FACET defaults to the :VALUE facet.
;;;    Returns the list of values stored on the FACET facet of the SLOT
;;;    slot of the object FRAME. The actual list within the frame is
;;;    returned, so surgery performed on the list of values returned by
;;;    FrameGet will change the frame. If no-demons is nil, will run
;;;    [<FACET> :get :after] demons.
;;;
;;; FRAMEGET-INTERNAL (frame slot &optional (facet :value))          [FUNCTION]
;;;    Internal version of frameget that does not execute demons.
;;;
;;; FRAMEGET! (frame slot &optional (facet :value) (no-demons t))    [FUNCTION]
;;;    Assumes that there is only one value in the FACET facet of the SLOT
;;;    slot of the object FRAME and returns it. (If there is more than one
;;;    value, the first one is returned.)
;;;
;;; INV-SLOT (slot)                                                  [FUNCTION]
;;;    Returns the inverse slot of SLOT, if it has one, otherwise nil.
;;;
;;; FRAMEGET-V-D (frame slot)                                        [FUNCTION]
;;;    First checks the :VALUE facet and returns the values if there are
;;;    any. If there are no values in the :VALUE facet, returns any values
;;;    present in the :DEFAULT facet of the frame's slot.
;;;
;;; HAS-SLOT (frame slot)                                            [FUNCTION]
;;;    Returns the tail of FRAME's slot list beginning with SLOT if
;;;    FRAME has a slot named SLOT; otherwise nil.
;;;
;;; SLOTS (frame)                                                    [FUNCTION]
;;;    Returns a list of the slots of the object FRAME.
;;;
;;; FACETS (frame slot)                                              [FUNCTION]
;;;    Returns a list of the facets of the SLOT slot of the object FRAME.
;;;
;;; SLOTNAMES (frame)                                                [FUNCTION]
;;;    Returns a list of the names of the slots of the object FRAME.
;;;
;;; FACETNAMES (frame slot)                                          [FUNCTION]
;;;    Returns a list of the names of the facets of the SLOT slot
;;;    of the object FRAME.
;;;
;;; FRAMEPUT (frame slot facet value &optional no-demons)            [FUNCTION]
;;;    Used for placing information into a frame.
;;;    Stores VALUE as one of the values of the FACET facet of the SLOT
;;;    slot of the object FRAME. If no-demons is nil, runs any [<FACET> :put
;;;    :after] demons. For example, the (:VALUE :PUT :AFTER) demon handles
;;;    inverse slot maintenance: If FACET is eq to :VALUE and SLOT has an
;;;    inverse, then FramePut also puts the object FRAME in the :VALUE facet
;;;    of the (Inv-Slot SLOT) slot of VALUE. If VALUE is already present,
;;;    does not run demons. Returns Value if it was stored, NIL otherwise.
;;;
;;; FRAMEPUT-INTERNAL (frame slot facet value)                       [FUNCTION]
;;;    Internal version of FramePut which does not execute demons.
;;;
;;; FRAMEPUT! (frame slot facet value &optional no-demons)           [FUNCTION]
;;;    Stores VALUE as the *unique* value of the FACET facet of the SLOT
;;;    slot of the object FRAME. It accomplishes this by first removing any
;;;    existing value(s) from the frame.
;;;
;;; ADD-VALUE (frame slot value &optional no-demons)                 [FUNCTION]
;;;    Adds a value to the :value facet of the frame's slot.
;;;
;;; MAKE-FRAME (name &rest slots)                                       [MACRO]
;;;    Defines a new frame named NAME with the specified SLOTS like
;;;    Def-Frame, but with side-effects. Works by calling frameput.
;;;
;;; FRPLFACET (frame slot facet values)                              [FUNCTION]
;;;    Stores VALUES as the values of the FACET facet of the SLOT slot 
;;;    of FRAME, replacing any previous values. Does not run any demons,
;;;    and so does not maintain inverse slot relationships.
;;;    This is a fast way to store multiple values. Reports an error if
;;;    VALUES is not a list.
;;;
;;; FRAMEREMOVE (frame slot facet value &optional no-demons)         [FUNCTION]
;;;    Deletes VALUE from the FACET facet of the SLOT slot of the object
;;;    FRAME. In no-demons is nil, runs any [<FACET> :remove :after]
;;;    demons. The demons include inverse-slot maintenance: If FACET is
;;;    :VALUE and SLOT has an inverse, then FrameRemove also removes FRAME
;;;    from the (Inv-Slot SLOT) :value of VALUE. Returns VALUE if it was
;;;    deleted, nil otherwise.
;;;
;;; FRAMEREMOVE-INTERNAL (framename slotname facetname value)        [FUNCTION]
;;;    Internal version of FrameRemove which does not execute demons.
;;;
;;; KILL-FACET (frame slot facet &optional no-demons)                [FUNCTION]
;;;    Deletes the entire FACET facet from the SLOT slot of the object
;;;    FRAME. Returns FACET if it was deleted, nil otherwise. If no-demons
;;;    is nil, runs any associated demons, such as inverse-slot maintenance.
;;;
;;; KILL-SLOT (frame slot &optional no-demons)                       [FUNCTION]
;;;    Deletes the entire SLOT slot of the object FRAME.
;;;    Returns SLOT if it was deleted, nil otherwise. If no-demons is
;;;    nil, runs any associated demons, such as inverse-slot maintenance.
;;;
;;; KILL-FRAME (frame &optional no-demons)                           [FUNCTION]
;;;    Deletes the object FRAME.
;;;    Returns FRAME if it was deleted, nil otherwise. If no-demons is
;;;    nil, runs any associated demons, such as inverse-slot maintenance.
;;;
;;; (SETF FRAMEGET) (value)                                      [SETF MAPPING]
;;;
;;; (SETF FRAMEGET!) (value)                                     [SETF MAPPING]
;;;
;;; MERGE-FRAME (mainframe mergee)                                   [FUNCTION]
;;;    Merges mergee into mainframe. If a slot was present in both MainFrame
;;;    and Mergee, all of its facets are seen as they were in MainFrame.
;;;    Surgery performed on Mergee will change MainFrame. Does not run any
;;;    demons, and so does not maintain inverse slot relationships.
;;;
;;; SHARE-SLOT (frame1 slot frame2)                                  [FUNCTION]
;;;    Makes FRAME2 share FRAME1's SLOT by destructive modification if
;;;    FRAME2 does not already have a slot named SLOT. Later surgery
;;;    performed on the contents of SLOT in either frame affects both
;;;    frames. For example, any value installed in FRAME1 or FRAME2 using
;;;    FramePut will be shared by both frames. Does not run any demons,
;;;    and so does not maintain inverse slot relationships.
;;;
;;; COPY-SLOTS (frame1 slots frame2 &optional facet-restrictions)    [FUNCTION]
;;;    Copies all slots in the list SLOTS from FRAME1 to FRAME2. 
;;;    Maintains inverse slot relationships. Facet-restrictions is a list
;;;    of facets to copy. If nil, all facets of the slots are copied.
;;;    Returns nil.
;;;
;;; @ (&optional frame slot facet value)                             [FUNCTION]
;;;    Indirection pointer to the data in another frame.
;;;    Behaves like FramePut if the first four arguments are non-NIL,
;;;    and like FrameGet if only the first three are non-NIL. If only
;;;    FRAME and SLOT are given, returns the list of SLOT's facets.
;;;    If only FRAME is given, returns the list of FRAME's slots.
;;;
;;; IMMEDIATE-PROGENY (frame paths)                                  [FUNCTION]
;;;    Returns the children of FRAME along the specified PATHS. PATHS
;;;    can be either a list of possible paths, or a single path.
;;;
;;; FRAMEGETCLASSES (frame &optional (path :ako))                    [FUNCTION]
;;;    Returns a list of the classes of a frame.
;;;
;;; TRANSITIVE-CLOSURE (frame &optional (slot :ako) (facet :value))  [FUNCTION]
;;;    Finds the transitive closure of FRAME by following paths specified
;;;    by SLOT/FACET by traversing the paths in a breadth-first manner.
;;;    Returns the set of all frames found without duplicates. Checks to
;;;    see if a frame has already been visited before proceeding, to
;;;    prevent infinite loops when cycles are encountered.
;;;
;;; LEAVES (frame &optional (slot :kindsof) (facet :value))          [FUNCTION]
;;;    Finds the leaf nodes (buds) of the tree rooted at FRAME by descending
;;;    SLOT/FACET paths by traversing the paths in a breadth-first
;;;    manner. Returns the set of all frames found without duplicates.
;;;    Checks to see if a frame has already been visited before
;;;    proceeding, to prevent infinite loops when cycles are encountered.
;;;
;;; PROGENY (frame &optional (slot :kindsof) (facet :value))         [FUNCTION]
;;;    Finds the progeny of FRAME by following SLOT/FACET paths by
;;;    traversing the paths in a breadth-first manner. Returns the
;;;    set of all frames found without duplicates. Checks to see if
;;;    a frame has already been visited before proceeding,
;;;    to prevent infinite loops when cycles are encountered.
;;;
;;; KILL-PATH (frame &optional (slot :kindsof) (facet :value))       [FUNCTION]
;;;    Kills FRAME and all of its progeny by following SLOT/FACET paths
;;;    by traversing the paths in a breadth-first manner. As each object
;;;    is destroyed, inverse slot relationships are maintained by
;;;    calling appropriate removal demons. This function is intended for
;;;    the destruction of temporary objects. Frame kernel objects are
;;;    protected against Kill-Path.
;;;    Returns the set of all frames found without duplicates.
;;;    Checks to see if a frame has already been visited before
;;;    proceeding, to prevent infinite loops when cycles are encountered.
;;;
;;; %FRAME (nil)                                                     [VARIABLE]
;;;    Global variable containing frame environment's frame arg
;;;    for use by demons.
;;;
;;; %SLOT (nil)                                                      [VARIABLE]
;;;    Global variable containing frame environment's slot arg
;;;    for use by demons.
;;;
;;; %FACET (nil)                                                     [VARIABLE]
;;;    Global variable containing frame environment's facet arg
;;;    for use by demons.
;;;
;;; %VALUE (nil)                                                     [VARIABLE]
;;;    Global variable containing frame environment's value arg
;;;    for use by demons.
;;;
;;; %OTHER-ARGS (nil)                                                [VARIABLE]
;;;    Global variable containing frame environment's other args
;;;    for use by demons.
;;;
;;; *VALUES-MODES* ('((:first \. some) (:no-values \. mapc)          [VARIABLE]
;;;                 (:append \. mapcan) (:collect \. mapcar)))
;;;    Global variable containing all methods frame-eval may use
;;;    to collect values from demon invocation.
;;;
;;; FRAME-EVAL (demons values-mode frame slot facet                  [FUNCTION]
;;;             &optional value other-args)
;;;    Binds %frame, %slot, %facet, %value and %other-args in the 
;;;    Frame Environment to the supplied values, and then runs
;;;    the demons, returning the result as specified by the values mode.
;;;    Possible values-modes include :FIRST, :NO-VALUES, :APPEND, and
;;;    :COLLECT. Demons is a list of demons, which are forms to be evaluated
;;;    in the frame environment.
;;;
;;; DEMON-P (demon)                                                  [FUNCTION]
;;;    Returns T if the frame is a demon.
;;;
;;; DEFINE-DEMON ((demon-frame &optional (demon-slot :demon)            [MACRO]
;;;               (demon-facet :value)) &body body)
;;;    Macro for defining a new demon. The first argument is the name of the
;;;    demon (i.e., where it is stored) followed by the body of the
;;;    definition. The name is of the form (demon-frame demon-slot
;;;    demon-facet), where demon-frame is the main name of the demon and the
;;;    slot and facet further characterize the demon's actions. Demons have
;;;    access to the frame environment, which consists of the global
;;;    variables %frame %slot %facet %value of the calling frame and
;;;    %other-args. 
;;;
;;; RUN-DEMON (demon-frame &optional (demon-slot :demon)             [FUNCTION]
;;;            (demon-facet :value) (values-mode :append) frame slot
;;;            facet value other-args)
;;;    Retrieves the demon definition and evaluates it in the frame 
;;;    environment using frame-eval. Values-mode specifies how values
;;;    are returned: no-values, append, collect, or just the first value.
;;;
;;; *CACHE-VALUES* (nil)                                             [VARIABLE]
;;;    If T, the result of FrameGet-Z demon invocation is cached in the
;;;    VALUE slot of the calling frame.
;;;
;;; FRAMEGET-Z (frame slot facet &key legal-demons (path :ako)       [FUNCTION]
;;;             (path-facet :value) path-focus ancestors-focus args
;;;             (cache-values *cache-values*) (values-mode :append))
;;;    Returns the same list as FrameGet, unless the frame object has
;;;    no slot-facet values, in which case a breadth-first search
;;;    is performed along the path relation from the frame until
;;;    such values are found. This enables slot values to be inherited
;;;    through network links. Information which is common to many objects
;;;    may be stored in a common ancestor (instead of redundantly storing
;;;    it in each object) and inherited by its progeny. Also
;;;    value-returns the unexplored queue.
;;;    LEGAL-DEMONS is a list of demons to try if the facet has no value.
;;;    For example, if we want to definitely check :DEFAULT and
;;;    :IF-NEEDED demons, instead of relying on frameget's demon invocation,
;;;    specify LEGAL-DEMONS as '(:DEFAULT :IF-NEEDED).
;;;    Path-focus is an extra path tried for the first frame. This is
;;;    useful for methods, where the first frame could be an instance of a
;;;    class instead of a class. Ancestors-focus is a list of ancestors to
;;;    be focused upon instead of starting the search at the frame -- this
;;;    is useful in method invocation where we sometimes want to consider
;;;    only a specific set of ancestors of the frame.
;;;    If cache-values is T, values from FrameGet-Z invocation are cached
;;;    in the :VALUE facet of the slot.
;;;      
;;;    Values-mode specifies how the values of demon invocation should be
;;;    returned.
;;;
;;; FRAMEGET-Z-LOCAL (frame slot facet dfacets                       [FUNCTION]
;;;                   &optional args (cache-values *cache-values*)
;;;                   (values-mode :append))
;;;    Returns the value of the first facet or demon-facet that has a value.
;;;
;;; IS (node supernode &optional (path :ako) (blockcats nil)         [FUNCTION]
;;;     visited)
;;;    Returns non-NIL if, following path links, node is a descendent of
;;;    supernode if supernode is an atom, or if node is a member of
;;;    supernode if supernode is a list. The search along path will ignore
;;;    blockcats. 
;;;
;;; CLASS-P (node)                                                   [FUNCTION]
;;;    Tests to see if its argument is a class.
;;;
;;; SUPERCLASSES (node)                                              [FUNCTION]
;;;    Returns the superclasses of a node.
;;;
;;; (SETF SUPERCLASSES) (value)                                  [SETF MAPPING]
;;;
;;; SUBCLASSES (node)                                                [FUNCTION]
;;;    Returns the subclasses of a node.
;;;
;;; (SETF SUBCLASSES) (value)                                    [SETF MAPPING]
;;;
;;; DEFCLASS (name superclasses &rest slots)                            [MACRO]
;;;    Defines a new class with the specified name, superclasses and slots.
;;;    Superclasses defaults to (THING) if not given by the user, so that
;;;    the class hierarchy is rooted at THING.
;;;
;;; SUBCLASS-P (node &optional (superclass :thing))                  [FUNCTION]
;;;    Tests to see if its argument is a subclass of superclass, which
;;;    defaults to the root class.
;;;
;;; SUPERCLASS-P (node &optional subclass)                           [FUNCTION]
;;;    Tests to see if its argument is a superclass of subclass, which
;;;    defaults to nil.
;;;
;;; INSTANCE-OF (node)                                               [FUNCTION]
;;;    Returns the CLASS of a node.
;;;
;;; (SETF INSTANCE-OF) (class)                                   [SETF MAPPING]
;;;
;;; INSTANCE-P (node)                                                [FUNCTION]
;;;    Tests to see if its argument is an instance, but doesn't care of what
;;;    frame it is an instance.
;;;
;;; INSTANCES (node)                                                 [FUNCTION]
;;;    Returns the instances of a node.
;;;
;;; IS-A-P (node supernode)                                          [FUNCTION]
;;;    Tests to see if NODE is a SUPERNODE by searching the class hierarchy.
;;;    Will traverse one CLASS link at the start of the search to
;;;    correctly process leaf instances, and then continues with :AKO links.
;;;    Returns the type of link (:CLASS or :AKO) or NIL.
;;;
;;; INSTANCE-NAME (type)                                                [MACRO]
;;;    Generates a new symbol, given the basic name of the frame.
;;;    This is used to guarrantee a unique frame name by adding a
;;;    numerical suffix to the name.
;;;
;;; MERGE-HERITAGE (frame class &key (path :ako)                     [FUNCTION]
;;;                 (path-facets '(:value)) slots-to-ignore)
;;;    Merges the structure pointed to by the FRAME with all the
;;;    corresponding structures of the frames accessible along the :AKO
;;;    link. SLOTS-TO-IGNORE is a list of the slots which shouldn't be
;;;    merged. Values are appended.
;;;
;;; MAKE-INSTANCE (class &rest slot-values-list)                     [FUNCTION]
;;;    Generates a new instance of the class: Creates a name for the
;;;    instance, a frame for the name, and links that frame to the class via
;;;    a CLASS link. Copies the default slot values inherited from the class
;;;    hierarchy into the instance and then initializes the supplied slot
;;;    values. Class, slotnames, and slot values must all be quoted. For
;;;    example, (make-instance 'elephant 'name "Clyde".
;;;    Returns the name of the instance.
;;;
;;; INITIALIZE-SLOTS (frame slot-values-list)                        [FUNCTION]
;;;    Initializes the values of the specified slots in frame, installing
;;;    them in the :value facet. Slot-values-list is a list of
;;;    alternating slot names and values.
;;;
;;; EXTRACT-DECLARATIONS (body &optional environment)                [FUNCTION]
;;;    Extracts the documentation string and declarations from a function
;;;    body. 
;;;
;;; DEFMETHOD ((message-name frame &optional (mode :method)) arglist    [MACRO]
;;;            &body body)
;;;    Defines a method for message MESSAGE-NAME for the FRAME object.
;;;    Mode is either :METHOD, :BEFORE or :AFTER, for regular methods,
;;;    before and after methods.
;;;
;;; *ANCESTORS-QUEUE* (nil)                                          [VARIABLE]
;;;    Global variable accessible to methods that contains a list that
;;;    represents the state of the queue in FrameGet-Z when this method
;;;    was found.
;;;
;;; *CALLING-FRAME* (nil)                                            [VARIABLE]
;;;    Global variable accessible to methods that contains the name of
;;;    the frame to which the message was sent.
;;;
;;; *MESSAGE-NAME* (nil)                                             [VARIABLE]
;;;    The name of the current message being processed.
;;;
;;; *MESSAGE-ARGUMENTS* (nil)                                        [VARIABLE]
;;;    The list of arguments of the current message being processed.
;;;
;;; *METHOD-TYPE* (:method)                                          [VARIABLE]
;;;    The type of method currently being applied (:method, :before, 
;;;    or :after).
;;;
;;; CALL-NEXT-METHOD "()"                                               [MACRO]
;;;    Calls the next method up in the calling hierarchy for this frame.
;;;
;;; SEND (frame message &rest args)                                  [FUNCTION]
;;;    Sends a message to the frame, and receives method(s) from the frame
;;;    for dealing with the message. Executes the methods in the frame
;;;    environment of the calling frame, along with any supplied
;;;    arguments. 
;;;
;;; RUN-METHODS (frame message args &optional (type :method)         [FUNCTION]
;;;              ancestors)
;;;    Sends MESSAGE to FRAME, retrieving any methods of the proper TYPE
;;;    (:METHOD, :AFTER, or :BEFORE). Calls the methods on the ARGS. If
;;;    ANCESTORS is supplied, it is used as the focus for where to begin
;;;    searching for methods.
;;;
;;; SAVE-FRAMES (&optional (filename "output.fwk")                   [FUNCTION]
;;;              (frames *frames*))
;;;    Pretty prints the frames created by FrameWork into a file. The frames
;;;    are both human readable and lisp readable (so that loading the
;;;    file restores the frames into lisp).
;;;
;;; SAVE-FRAME (frame &key (stream *standard-output*))               [FUNCTION]
;;;
;;; *DEFAULT-PPFRAME-INDENT* (3)                                     [VARIABLE]
;;;    Indentation factor: amount the indent is increased 
;;;    at each additional level.
;;;
;;; PPF (frame &optional (stream *standard-output*)                  [FUNCTION]
;;;      &key (readable t) (indent 0))
;;;    A synonym for pprint-frame.
;;;
;;; PPRINT-FRAME (frame &optional (stream *standard-output*)         [FUNCTION]
;;;               &key (readable t) (indent 0))
;;;    If readable is NIL, parentheses are omitted.
;;;
;;; *MAX-LEVELS* (3)                                                 [VARIABLE]
;;;    Maximum number of levels in a Frame.
;;;
;;; PPRINT-FRAME-INTERNAL (frame stream &optional (readable t)       [FUNCTION]
;;;                        (indent 0) (level 0))
;;;
;;; *FRAMEWORK-PROMPT* ("~%fw> ")                                    [VARIABLE]
;;;    Prompt used in the FrameWork Listener.
;;;
;;; *PRINT-FRAME-BODIES* (t)                                         [VARIABLE]
;;;    If the result of a command execution is the name of a frame, the
;;;    frame body will be printed and the name returned.
;;;
;;; *FRAMEWORK-COMMANDS* (nil)                                       [VARIABLE]
;;;    List of defined commands for the listener.
;;;
;;; FRAMEWORK-COMMAND (name short-doc long-doc function)            [STRUCTURE]
;;;
;;; DEFINE-FW-LISTENER-COMMAND (name arg-list short-doc long-doc        [MACRO]
;;;                             &body body)
;;;    Defines a new command for the FrameWork listener. Name is either the
;;;    name of the command, or a list of synonyms. Short-doc is for the
;;;    summary help display. Long-doc is what should be displayed when
;;;    asking for detailed help on the command. If the last form in the
;;;    body is :noprint, the result of evaluating the command is not
;;;    printed. When called from the listener, the rest of the line is
;;;    received as arguments.
;;;
;;; DELETE-COMMAND (name)                                            [FUNCTION]
;;;    Deletes a FrameWork listener command.
;;;
;;; FIND-COMMAND (name)                                              [FUNCTION]
;;;    Finds the FrameWork listener command with that name or nickname.
;;;
;;; LISTIFY-STRING (string)                                          [FUNCTION]
;;;    Turns a string into a list of symbols.
;;;
;;; *SCHEDULE* (nil)                                                 [VARIABLE]
;;;    A list of actions which are executed once every tick of the clock.
;;;    They must have bounded execution time.
;;;
;;; GET-INPUT (&optional (stream *standard-input*))                  [FUNCTION]
;;;    Gets input from the user. If the user isn't typing anything, runs
;;;    any functions found on the *schedule*.
;;;
;;; LISTENER "()"                                                    [FUNCTION]
;;;    A READ-EVAL-PRINT loop for convenient interaction with FrameWork and
;;;    demoing the system. Interprets framework commands in abbreviated
;;;    form, without parentheses and quotes. Typing the name of a frame will
;;;    display it pretty printed. Frames created using the listener are
;;;    accessible to the save-frame utility.
;;;
;;; FRAMEWORK-EVAL (line)                                            [FUNCTION]
;;;    Evaluates commands typed to the framework listener by the user.
;;;    If the line begins with a symbol, and that symbol represents a
;;;    framework listener command, the apropriate command is called
;;;    with the rest of the line as input. If the symbol is the name
;;;    of a frame, it is pretty printed. Otherwise the line is treated
;;;    like a regular lisp form.
;;;
;;; EXPLODE (symbol)                                                 [FUNCTION]
;;;
;;; IMPLODE (list)                                                   [FUNCTION]
;;;
;;; CRUSH (a b)                                                      [FUNCTION]
;;;
;;; *PROPERTIES-ARE-SYMBOLS* (nil)                                   [VARIABLE]
;;;    If T, properties are represented as P and ~P. 
;;;    If NIL, properties are represented as P and (NOT P).
;;;
;;; NEGATE (property)                                                [FUNCTION]
;;;    Forms the negation of property.
;;;
;;; HAS-PROPERTY (frame property &optional (path :ako)               [FUNCTION]
;;;               (path-facet :value) (property-slot :ako)
;;;               (property-facet :mode))
;;;    Checks whether FRAME has the given PROPERTY. Property values are
;;;    stored on the MODE facet of the :AKO slot, and may be inherited
;;;    in a breadth-first manner from ancestors along the :AKO path. The
;;;    inheritance of a given property P may be blocked by the property
;;;    ~P (NOT P) occurring somewhere along the path from FRAME to the
;;;    ancestor with the property P. This provides for inheritance with
;;;    exceptions. 
;;;
;;; TREE-PATH (frame paths &optional (restrict nil)                  [FUNCTION]
;;;            (show-frame nil) (visited nil))
;;;    Constructs a tree from FRAME's inheritance along PATHS, suitable
;;;    for displaying using a graphing function. The resulting tree is
;;;    of the form (root subtree1 subtree2 ...) where each subtree is
;;;    of the same form. If SHOW-FRAME is T, includes the actual frame
;;;    structure of the leaves. RESTRICT is either a maximum depth,
;;;    a property, or a function of the form (FUNCALL <function> .
;;;    <args>). If RESTRICT is a property, only nodes with that property are
;;;    shown, with intermediate nodes visible, of course.
;;;
;;; FRAME-REP (frame restrict &optional show-if-fails show-frame)    [FUNCTION]
;;;    Creates a representation for the frame as a node in the graph.
;;;
;;; *SHOW-PARENTHESES* (t)                                           [VARIABLE]
;;;    If T, shows the parentheses around the values.
;;;
;;; TREE-COPY (tree &optional (keyp t)                               [FUNCTION]
;;;            (show-parens *show-parentheses*))
;;;    Returns a copy of TREE (a frame). If show-parens is T, puts 
;;;    parentheses around the values. This is useful for display them as
;;;    individual nodes of the frame, instead of just a big list.
;;;
;;; *PATH-SPECIAL-SYMBOLS* ('(demon ako kindsof value default        [VARIABLE]
;;;                         if-needed if-added if-removed if-fetched
;;;                         mode put get remove after before method
;;;                         class instances thing type types parent
;;;                         child part-of parts is-component-of
;;;                         components))
;;;    Symbols which should be treated as if they were in the keyword
;;;        package for path reading.
;;;
;;; PATH-READER (stream char)                                        [FUNCTION]
;;;    Reader macro which reads in a special path syntax. For example,
;;;         $!cat.ako --> MAMMAL
;;;         $cat.ako  --> (MAMMAL SIAMESE).
;;;
;;; PATH-GET! (frame &rest path)                                     [FUNCTION]
;;;    Extracts the value at the end of the path beginning at frame
;;;    using frameget!. E.g., (path-get! me 'office 'room-number).
;;;    Here a path is a series of slots.
;;;
;;; PATH-GET (frame &rest path)                                      [FUNCTION]
;;;    Extracts the values at the end of the path beginning at frame
;;;    using frameget. E.g., (path-get me 'office 'room-number).
;;;    Here a path is a series of slots.
;;;
;;; DEFINE-INVERSE-SLOTS (slot1 slot2)                               [FUNCTION]
;;;    Defines two slots as slots and inverses of each other.
;;;


;;; ****************************************************************
;;; FrameWork Kernel ***********************************************
;;; ****************************************************************

;;; Let's be smart about CLtL2 compatible Lisps:
(eval-when (compile load eval)
  #+(or (and :excl (or :allegro-v4.0 :allegro-v4.1))
	:mcl
	(and :lucid :lcl4.0)
	(and :cmu :new-compiler)
	:clisp
	)
  (pushnew :cltl2 *features*))

#-:cltl2
(in-package "FRAMEWORK" :nicknames '("FW"))
#-:cltl2
(shadow '(defclass make-instance defmethod call-next-method) "FW")

#+:cltl2
(defpackage "FRAMEWORK" (:nicknames "FW") 
  (:shadow defclass make-instance defmethod call-next-method)
  (:use #-:lucid "COMMON-LISP"
	#+:lucid "LISP" #+:lucid "LUCID-COMMON-LISP"))
#+:cltl2
(unless (find-package "FRAMEWORK") 
  (make-package  "FRAMEWORK" :nicknames '("FW"))
  (shadow '(defclass make-instance defmethod call-next-method) "FW")
  (use-package '("COMMON-LISP") "FW"))
#+:cltl2
(in-package "FRAMEWORK")

(pushnew :framework *features*)

(export '(*version* *frames* *system-frames*
	  Frame Frame+ FrameP
	  Def-Frame Create-Frame
	  Delete-Frame Delete-Frames
	  FrameAssoc FrameAssoc+
	  FrameGet FrameGet! FrameGet-V-D
	  FramePut FramePut! Add-Value
	  FrameRemove Kill-Frame Kill-Slot Kill-Facet
	  FrplFacet
	  Inv-Slot
	  Slots SlotNames Facets FacetNames Has-Slot GetTail
	  Merge-Frame Share-Slot Copy-Slots @
	  Immediate-Progeny
	  FrameGetClasses Transitive-Closure Leaves Progeny Kill-Path
	  Demon-P Define-Demon Frame-Eval Run-Demon
	  FrameGet-Z *cache-values*
	  Class-P Superclasses Subclasses DefClass Subclass-P Superclass-P
	  Instance-Of Instance-P Instances 
	  Defmethod Make-Frame Make-Instance Send Call-Next-Method 
	  Is-A-P Is
	  Save-Frames Save-Frame 
	  PPF PPrint-Frame *default-ppframe-indent*
	  Listener *print-frame-bodies* Define-Fw-Listener-Command
	  Has-Property Negate Tree-Path Tree-Copy *Show-Parentheses*
	  Path-Get Path-Get!
	  Define-Inverse-Slots
	  %frame %slot %facet %value %other-args
	  ))

;;; ********************************
;;; Global Variables ***************
;;; ********************************
(defparameter *version* "2.1  THU 18-MAR-93 23:33:04"
  "Current version number/date for FrameWork.")

;;; Should we have globals for default inheritance link and facet?
;;; These globals currently aren't used in the functions. 
(defvar *default-inheritance-link* :ako
  "Default link used for inheritance in FrameWork.")
(defvar *default-inheritance-facet* :value
  "Default facet used for inheritance in FrameWork.")

;;; ********************************
;;; Copyright and Herald ***********
;;; ********************************
(defun framework-copyright (&optional (stream *standard-output*))
  "Prints a FrameWork copyright notice and header upon startup."
  (format stream "~%;;; ~V,,,'*A" 73 "*")
  (format stream "~%;;;   FrameWork: A Frame Knowledge Representation System.")
  (format stream "~%;;;   Version ~A." *version*)
  (format stream "~%;;;   Written by Mark Kantrowitz, CMU School of Computer Science.")
  (format stream "~%;;;   Copyright (c) 1990-93. All rights reserved.")
  (format stream "~%;;; ~V,,,'*A~%" 73 "*")
  (force-output stream))
(framework-copyright)

(defun current-time-string (&optional (mode 'hyphen))
  "Returns a string for the current time and date in a variety of modes."
  (multiple-value-bind (secs min hour date month year dow) (get-decoded-time)
    (case mode
      (hyphen
       (string-upcase 
	(format nil "~A ~A ~A"
		(dow-string dow 'short)
		(date-string month date year 'hyphen)
		(time-string hour min secs))))
      (long
       (format nil "~A, ~A, ~A"
		(dow-string dow 'long)
		(date-string month date year 'long)
		(time-string hour min secs 'ampm))))))

(defun date-string (month date year &optional (mode 'hyphen))
  "Given a date, returns a string for the date in a variety of modes."
  (case mode
    (hyphen
     (format nil "~A-~A-~A" 
	     date
	     (month-string month 'short)
	     (year-string year 'short)))
    (slash
     (format nil "~A/~A~@[/~A~]"
	     month date (year-string year 'short)))
    (long
     (format nil "~A ~D~@[, ~A~]"
	     (month-string month 'long)
	     date
	     (year-string year 'long)))))

(defun year-string (year &optional (mode 'long))
  "Formats a year number in various ways."
  (when year
    (case mode
      (long (format nil "~A" year))
      (short (format nil "~A" (mod year 100))))))

(defun time-string (hour min secs &optional (mode 'full))
  "Formats the current time in a variety of ways."
  (case mode
    (full
     (format nil "~2,'0d:~2,'0d:~2,'0d" hour min secs))
    (ampm
     (multiple-value-bind (ampm h) (floor hour 12)
       (when (zerop h) (setf h 12))
       (when (= hour 12) (setf ampm 0))
       (format nil "~d:~2,'0d:~2,'0d ~[am~;pm~]"
	       h min secs ampm)))))

(defun dow-string (dow &optional (mode 'short))
  "Formats the day of week in a variety of modes."
  (case mode
    (letter
     (svref '#("M" "T" "W" "R" "F" "S" "U") dow))
    (abbrev
     (svref '#("M" "T" "W" "R" "F" "Sa" "Su") dow))
    (short
     (svref '#("Mon" "Tue" "Wed" "Thu" "Fri" "Sat" "Sun") dow))
    (long
     (svref '#("Monday" "Tuesday" "Wednesday" "Thursday"
	       "Friday" "Saturday" "Sunday") dow))))

(defun month-string (month &optional (mode 'short))
  "Formats the month in a variety of ways."
  (case mode
    (short
     (svref '#(0 "Jan" "Feb" "Mar" "Apr" "May"
		 "Jun" "Jul" "Aug" "Sep" "Oct"
		 "Nov" "Dec")
	    month))
    (long 
     (svref '#(0 "January" "February" "March" "April" "May"
		 "June" "July" "August" "September" "October"
		 "November" "December")
	    month))))

(defun Framework-Herald (&optional (stream *standard-output*))
  "Prints a FrameWork Herald. Does basic copyright statement,
   as well as the time and date."
  (framework-copyright stream)
  (format stream "~&;;; ~A" (current-time-string 'long)))

;;; ********************************
;;; Primitives *********************
;;; ********************************
(defun eqmemb (item list &key (test #'equal))
  "Checks whether ITEM is either equal to or a member of LIST."
  (if (listp list)
      (member item list :test test)
    (funcall test item list)))

(defun neq (x y)
  "not eq"
  (not (eq x y)))

(defun car-eq (x y)
  "Checks whether Y is eq to the car of X."
  (and (listp x)
       (eq (car x) y)))

(defun dremove (item list)
  "Destructive remove which replaces the original list with the list
   that results when ITEM is deleted from LIST."
  ;; This is safe only because of the way delete works.
  (displace list (delete item list :test #'eq)))

(defun displace (list val)
  "Replaces LIST with VAL by destructively modifying the car and cdr of LIST.
   Warning: VAL must not share list structure with LIST or you'll be sorry."
  (when list
    ;; Can't alter NIL.
    (rplaca list (car val))
    (rplacd list (cdr val))))

(defun tailpush (item list)
  "Pushes ITEM onto the tail of LIST. Does not work if the list is null."
  (when list
    (rplacd (last list) (list item))))

;;; ********************************
;;; Macros *************************
;;; ********************************
(defmacro do-queue (((&optional (node 'node) (queue 'queue) 
				(children 'children)
				visited) ; if visited is nil, not maintaind
		     initial-queue
		     children-form
		     &optional
		     (dequeue-form '(pop queue))
		     (merge-form '(setq queue (append queue progeny)))
		     result-form)
		    &body body)
  "Implements generic search using a queue representation. 
   If the VISITED iteration variable is specified, checks to see if a
   node has already been visited before proceeding, to prevent infinite
   loops in the search when cycles are encountered. It also prevents 
   multiple occurrences of a node when several inheritance paths lead
   to the same node. If VISITED is specified, it is the name of the
   variable where the search history is maintained."
  `(let ((,queue ,initial-queue)
	 ,@(if visited (list `(,visited nil)))) ; to avoid cycles
     (loop
      (when (null ,queue) (return ,result-form))
      (let ((,node ,dequeue-form))
	;; Check to see if the frame has already been visited before 
	;; proceeding. Prevents infinite loops when a cycle is encountered.
	;; Also prevents multiple occurrences of a node when several
	;; inheritance paths lead to the same node.
	(unless ,(when visited `(member ,node ,visited))
	  ;; Add the node to the visited list.
	  ,@(when visited (list `(push ,node ,visited)))
	  ;; Merge the progeny into the queue. Appending to the end
	  ;; of the queue leads to breadth-first search. Appending
	  ;; to the beginning of the queue leads to depth-first search.
	  (let ((,children ,children-form))
	    ;; merge-form must come before body so that if the body
	    ;; is saving the queue, it gets the entire queue. 
	    ,merge-form			
	    ,@body))))))

;;; ********************************
;;; Frame Storage ******************
;;; ********************************
(defvar *frame-table* (make-hash-table :test #'equal)
  "Hash table where all the frame definitions are stored. 
   Since we are using a hash table instead of a property list, the
   frame name need not be an atom. This allows us to attach information
   to any lisp object.")

(defvar *frames* ()
  "Global list of the names of all user defined frames.")

(defvar *system-frames* nil
  ;; Maybe these frames should be protected from user modification?
  "Global list of all system defined frame names. These frames define
   the default relations (slots) and their inverses. Frames included
   on this list are normally invisible to user deleting and saving
   operations.")

(defun Define-Frame (name frame)
  "Internal function for creating a new frame. Pushes the name of the 
   frame onto the list of user defined frames."
  (pushnew name *frames*)
  (setf (gethash name *frame-table*) frame)
  frame)  

(defun Create-Frame (name)
  "Creates a new blank frame named NAME."
  (define-frame name (list name)))

(defmacro Def-Frame (name frame)
  "External function for creating a new frame. The name and
   frame do not need to be quoted."
  ;; this is the external interface.
  `(progn
     (define-frame ',name ',frame)
     ',name))

(defun Frame (name)
  "Returns the frame \"property\" (frame structure) of NAME if there is one;
   otherwise returns nil."
  (gethash name *frame-table*))

(defun Frame+ (framename)
  "Gets the frame associate with framename. If a frame structure does
   not already exist, creates a new one and returns it."
  ;; + is used here as a create-if-not-present marker. see frameassoc+ too.
  (or (Frame framename)
      (Create-Frame framename)))

(defun FrameP (name)
  "Predicate which returns T if NAME names a defined frame, nil otherwise."
  (not (null (Frame name))))

;;; maybe call this erase-frame?
(defun Delete-Frame (frame)
  "Deletes a frame definition without removing any references 
   to the frame in other frames."
  ;; remove it from the list of defined frames
  (setf *frames* (delete frame *frames*))
  ;; remove the definition
  (remhash frame *frame-table*))

(defun Delete-Frames (&optional (frame-list *frames*))
  "Deletes a specified list of frames, which defaults to all user
   defined frames. Evaluating (delete-frames) is a quick way to
   undo your work without eliminating the system defined frames."
  ;; note that the frame-list *frames* does not include system frames
  (dolist (frame frame-list)
    (delete-frame frame)))

;;; ********************************
;;; Kernel *************************
;;; ********************************
;;; General Frame-Related Functions for Getting and Putting
;;; These are general functions which make generalizing FrameWork easy.

;;; Frames are implemented as nested association lists called flists 
;;; after the notation used in FRL:
;;;    flist   ::= (key . bucket)
;;;    key     ::= s-expression
;;;    bucket  ::= (item*) | (value*) | NIL
;;;    item    ::= flist
;;;    value   ::= s-expression
;;; A path is a sequence of keys used to access a value. A frame structure
;;; is the top-level flist stored as the frame property of the frame's
;;; name (which is also the key of this flist).

;;; FrameGet/FramePut/... are essentially the following functions using
;;; Frame and Frame+ to extract the top level flist. We aren't currently
;;; using them much, but give them here as an example of how FrameWork could
;;; be extended to more levels.

(defun Flistp (flist)
  "Returns T if the FLIST is a flist."
  (listp flist))

(defun Flist-Key (flist)
  "Returns the key of a flist."
  (and (flistp flist)
       (car flist)))

(defun Flist-Bucket (flist)
  "Returns the bucket of a flist."
  (and (flistp flist)
       (cdr flist)))

(defun Flist-Keys (flist)
  "Returns a list of the keys of the items in the bucket of flist."
  (and (flistp flist)
       (mapcar #'flist-key (flist-bucket flist))))

(defun FrameAssoc (key flist &key (test #'eq))
  "Finds the item with key KEY in the FLIST if present."
  (assoc key (rest flist) :test test))

(defun FrameAssoc+ (key flist &key (test #'eq))
  "Finds item with key KEY in the FLIST if present, otherwise inserts it. 
   Returns the entry."
  (or (frameassoc key flist :test test)
      (let ((new (list key)))
	(tailpush new flist)
	new)))

(defun Flist-Get (flist &rest path)
  "Follows the key path down to the value. For retrieving items from
   an flist."
  (let ((item flist))
    (dolist (key path)
      ;; If the embedding has ended, quit now.
      (when (null item) (return nil))
      (setf item (frameassoc key item)))
    (flist-bucket item)))

(defun Flist-Put (flist item &rest path)
  "Stores ITEM in the bucket pointed to by the path of keys.
   Returns the modified FLIST."
  (let ((temp flist))
    (dolist (key path)
      (setf temp (frameassoc+ key temp)))
    (unless (member item temp)
      (tailpush item temp))
    flist))

(defun Flist-Delete (flist &rest path)
  "Deletes the entire item accessed. Returns the modified FLIST."
  (let ((old flist)
	(temp flist))
    (dolist (key path)
      (setf old temp
	    temp (frameassoc key temp)))
    (dremove temp old)
    flist))

(defun Flist-Clear (flist &rest path)
  "Deletes the bucket of the indicated item, but leaves the key.
   Returns the modified FLIST."
  (let ((temp flist))
    (dolist (key path)
      (setf temp (frameassoc key temp)))
    (rplacd temp nil)
    flist))

(defun Flist-Replace (flist item &rest path)
  "Replaces all existing items with the item. Returns the modified FLIST.
   Equivalent to Flist-Clear followed by Flist-Put."
  (let ((temp flist))
    (dolist (key path)
      (setf temp (frameassoc key temp)))
    (rplacd temp (list item))
    flist))

;;; ********************************
;;; Accessing and Modifying Objects 
;;; ********************************

;;; FrameGet, FramePut and FrameRemove have 2 versions:
;;;    o  the -internal function which does not run demons
;;;    o  the main function which does, controlled by an optional
;;;       argument (which defaults to allowing in put and remove,
;;;       and disallowing in get).
;;; The demons run in each are very general and hang off of the facets.
;;; For example, putting data in the :VALUE facet of a frame triggers
;;; the [:VALUE :PUT :AFTER] demon which runs the [:IF-ADDED :DEMON :VALUE]
;;; demon which executes the local :IF-ADDED demon located in the :IF-ADDED
;;; facet of the slot.
;;;
;;; In general, we don't run the :IF-ADDED/:IF-NEEDED demons if the value
;;; was already there. For this reason it is extremely important that
;;; the frameput-internal and frameremove-internal functions return nil
;;; if there was no need for the function to run. This eliminates the
;;; possibility of cycles.
;;;
;;; Should all the parent :IF-ADDED demons also be run? (inherited behaviors)

;;; Functions for Fetching Information from an Object: Getting Functions

;; Frames store a list of values. Thus (nil) would represent a value
;; of NIL, while () would represent "no values".

(defun FrameGet (frame slot &optional (facet :value) (no-demons t))
  "Fetches information from a frame given an access path consisting of
   a frame, a slot, and a facet. FACET defaults to the :VALUE facet.
   Returns the list of values stored on the FACET facet of the SLOT slot
   of the object FRAME. The actual list within the frame is returned, so
   surgery performed on the list of values returned by FrameGet will
   change the frame. If no-demons is nil, will run [<FACET> :get :after] 
   demons. "
  ;; Having demons in FrameGet is risky because demon invocation itself
  ;; calls frameget. This could potentially result in infinite loops.
  ;; So we have no-demons default to T to prevent demon
  ;; invocation in the default case. We must make sure that the frameget
  ;; in run-demons has no-demons set to T.
  ;; Perhaps we should rely only on FrameGet-Z for demon invocation?
  (let ((result (frameget-internal frame slot facet)))
    (cond ((and (null result) (not no-demons))
	   ;; if more than one :IF-NEEDED demon is present, the values
	   ;; are appended together.
	   (run-demon facet :get :after :append frame slot facet nil))
	  (t
	   result))))

(defun FrameGet-Internal (frame slot &optional (facet :value))
  "Internal version of frameget that does not execute demons."
  (cdr (assoc facet (facets frame slot))))

(defun FrameGet! (frame slot &optional (facet :value)(no-demons t))
  "Assumes that there is only one value in the FACET facet of the SLOT slot
   of the object FRAME and returns it. (If there is more than one value,
   the first one is returned.)"
  ;; ! = unique (car)
  (car (frameget frame slot facet no-demons)))

(defun Inv-Slot (slot)
  "Returns the inverse slot of SLOT, if it has one, otherwise nil."
  (FrameGet! slot :INVERSE :VALUE))

(defun FrameGet-V-D (frame slot)
  "First checks the :VALUE facet and returns the values if there are any.
   If there are no values in the :VALUE facet, returns any values present
   in the :DEFAULT facet of the frame's slot."
  (or (FrameGet frame slot :VALUE)
      (FrameGet frame slot :DEFAULT)))

(defun Has-Slot (frame slot)
  "Returns the tail of FRAME's slot list beginning with SLOT if
   FRAME has a slot named SLOT; otherwise nil."
  (member slot (Slots frame) :key #'car :test #'eq))

(defun Slots (frame)
  "Returns a list of the slots of the object FRAME."
  (cdr (frame frame)))

(defun Facets (frame slot)
  "Returns a list of the facets of the SLOT slot of the object FRAME."
  (cdr (assoc slot (slots frame))))

(defun SlotNames (frame)
  "Returns a list of the names of the slots of the object FRAME."
  (mapcar #'car (slots frame)))

(defun FacetNames (frame slot)
  "Returns a list of the names of the facets of the SLOT slot
   of the object FRAME."
  (mapcar #'car (facets frame slot)))

;;; Functions for Storing a Value into an Object: Putting Functions

(defun FramePut (frame slot facet value &optional no-demons)
  "Used for placing information into a frame.
   Stores VALUE as one of the values of the FACET facet of the SLOT slot
   of the object FRAME. If no-demons is nil, runs any [<FACET> :put :after] 
   demons. For example, the (:VALUE :PUT :AFTER) demon handles
   inverse slot maintenance: If FACET is eq to :VALUE and SLOT has an inverse,
   then FramePut also puts the object FRAME in the :VALUE facet of the
   (Inv-Slot SLOT) slot of VALUE. If VALUE is already present, does not run
   demons. Returns Value if it was stored, NIL otherwise."
  (when (and frame slot facet)
    (let ((result (frameput-internal frame slot facet value)))
      (when (and result (not no-demons))
	(run-demon facet :put :after :no-values frame slot facet value)))
    value))

(defun FramePut-Internal (frame slot facet value)
  "Internal version of FramePut which does not execute demons."
  (when (and frame slot facet)
    (let ((values (FrameAssoc+ facet (FrameAssoc+ slot (Frame+ frame)))))
      ;; Only adds a value if it is not already present.
      (unless (member value values :test #'eq) 
	(tailpush value values)))))

(defun FramePut! (frame slot facet value &optional no-demons)
  "Stores VALUE as the *unique* value of the FACET facet of the SLOT slot
   of the object FRAME. It accomplishes this by first removing any 
   existing value(s) from the frame."
  (dolist (val (FrameGet frame slot facet))
    (FrameRemove frame slot facet val no-demons))
  (FramePut frame slot facet value no-demons))

(defun Add-Value (frame slot value &optional no-demons)
  "Adds a value to the :value facet of the frame's slot."
  (frameput frame slot :value value no-demons))

(defmacro Make-Frame (name &rest slots)
  "Defines a new frame named NAME with the specified SLOTS like Def-Frame,
   but with side-effects. Works by calling frameput."
  (let ((forms nil))
    (dolist (slot slots)
      (let ((slotname (car slot)))
	(dolist (facet (cdr slot))
	  (let ((facetname (car facet)))
	    (dolist (value (cdr facet))
	      (push `(frameput ',name ',slotname ',facetname ',value)
		    forms))))))
    `(progn ,@forms)))

(defun FrplFacet (frame slot facet values)
  "Stores VALUES as the values of the FACET facet of the SLOT slot 
   of FRAME, replacing any previous values. Does not run any demons, 
   and so does not maintain inverse slot relationships.
   This is a fast way to store multiple values. Reports an error if
   VALUES is not a list."
  (if (not (listp values)) 
      (format t "~&FrplFacet: <values> argument must be a list.")
    (rplacd (FrameAssoc+ facet (FrameAssoc+ slot (Frame+ frame)))
	    values)))

;;; Functions for Removing Information from an Object: Removing Functions

(defun FrameRemove (frame slot facet value &optional no-demons)
  "Deletes VALUE from the FACET facet of the SLOT slot of the object
   FRAME. In no-demons is nil, runs any [<FACET> :remove :after] demons.
   The demons include inverse-slot maintenance: If FACET is :VALUE and
   SLOT has an inverse, then FrameRemove also removes FRAME from the
   (Inv-Slot SLOT) :value of VALUE. Returns VALUE if it was deleted,
   nil otherwise."
  ;; Rename this to Kill-Value and rename frame-remove-internal
  ;; as FrameRemove, so that kill- has side-effects, frame- doesn't?
  (let ((result (frameremove-internal frame slot facet value)))
    (when (and result (not no-demons))
      (run-demon facet :remove :after :no-values frame slot facet value))
    result))

(defun FrameRemove-Internal (framename slotname facetname value)
  "Internal version of FrameRemove which does not execute demons."
  ;; Returns value if deleted anything, nil otherwise.
  ;; maybe we should have a (not (null target)) to make it t/nil?
  ;; (no side effects)
  (let* ((frame (frame FrameName))
	 (slot (FrameAssoc SlotName frame))
	 (facet (FrameAssoc FacetName slot))
	 (target (car (member VALUE (cdr facet) :test #'eq))))
    (and target
	 (null (cdr (dremove target facet)))
	 (null (cdr (dremove facet slot)))
	 (null (cdr (dremove slot frame)))
	 (delete-frame FrameName))
    target))

(defun Kill-Facet (frame slot facet &optional no-demons)
  "Deletes the entire FACET facet from the SLOT slot of the object FRAME.
   Returns FACET if it was deleted, nil otherwise. If no-demons is nil,
   runs any associated demons, such as inverse-slot maintenance."
  (let ((values (FrameGet frame slot facet)))
    (when values
      (dolist (value values facet)
	(FrameRemove frame slot facet value no-demons)))))

(defun Kill-Slot (frame slot &optional no-demons)
  "Deletes the entire SLOT slot of the object FRAME.
   Returns SLOT if it was deleted, nil otherwise. If no-demons is nil,
   runs any associated demons, such as inverse-slot maintenance."
  (let ((facets (Facets frame slot)))
    (when facets
      (dolist (facet facets slot)
	(Kill-Facet frame slot (car facet) no-demons)))))

(defun Kill-Frame (frame &optional no-demons)
  "Deletes the object FRAME.
   Returns FRAME if it was deleted, nil otherwise. If no-demons is nil,
   runs any associated demons, such as inverse-slot maintenance."
  (let ((slots (Slots frame)))
    (when slots
      (dolist (slot slots frame)
	(Kill-Slot frame (car slot) no-demons)))))

;;; Other random kernel functions

;; Defsetf for frameget
(defsetf frameget (frame slot &optional (facet ':value)) (value)
  `(frameput ,frame ,slot ,facet ,value))
(defsetf frameget! (frame slot &optional (facet ':value)) (value)
  `(frameput! ,frame ,slot ,facet ,value))

;;; Sharing Structure Between Frames:

(defun Merge-Frame (Mainframe Mergee)
  "Merges mergee into mainframe. If a slot was present in both MainFrame
   and Mergee, all of its facets are seen as they were in MainFrame. Surgery
   performed on Mergee will change MainFrame. Does not run any demons, 
   and so does not maintain inverse slot relationships."
  (rplacd (last (Frame MainFrame))
          (cdr (Frame Mergee))))

(defun Share-Slot (frame1 slot frame2)
  "Makes FRAME2 share FRAME1's SLOT by destructive modification if
   FRAME2 does not already have a slot named SLOT. Later surgery 
   performed on the contents of SLOT in either frame affects both
   frames. For example, any value installed in FRAME1 or FRAME2 using
   FramePut will be shared by both frames. Does not run any demons, 
   and so does not maintain inverse slot relationships." 
  (or (Has-Slot frame2 slot)
      (tailpush (FrameAssoc+ slot (Frame+ frame1))
		(Frame+ frame2))))

(defun Copy-Slots (frame1 slots frame2 &optional facet-restrictions)
  "Copies all slots in the list SLOTS from FRAME1 to FRAME2. 
   Maintains inverse slot relationships. Facet-restrictions is a list
   of facets to copy. If nil, all facets of the slots are copied.
   Returns nil."
  (dolist (slotname slots)
    (dolist (facet (facets frame1 slotname))
      (let ((facetname (car facet)))
	(when (or (null facet-restrictions)
		  (find facetname facet-restrictions))
	  (dolist (value (cdr facet))
	    (frameput frame2 slotname facetname value)))))))

;;; Indirection:

;;;     Including (@ frame slot facet) as a value of a frame may be
;;;     used to point to data in another frame. This form will be
;;;     evaluated during demon invocation. 
;;; Evaluation and Indirection are mutually exclusive (since indirection
;;; is implemented by evaluation...).
;;; Should indirection pointers be recursively evaluated? Probably yes.
;;; Should the values of indirection pointers be merged (via append)
;;; into the list of values returned, or just included as a single
;;; value? Should @ behave like frameget! or frameget? 

;;; The Non-Atomic Slot Convention:
;;; Maybe the arguments to frameget should always be evaluated, so that
;;; non-atomic slots get evaluated. See comments on page 10 of FRL manual.
;;; If slot is non-atomic, eval it to get the actual value of the slot
;;; (i.e., so (@ frame slot) can be used for slot indirection or
;;; have arbitrary forms for fancier stuff). have frame/slot in the env
;;; when evaling it? what about inverse-slot maintenance?

(defun @ (&optional frame slot facet value)
  "Indirection pointer to the data in another frame.
   Behaves like FramePut if the first four arguments are non-NIL,
   and like FrameGet if only the first three are non-NIL. If only
   FRAME and SLOT are given, returns the list of SLOT's facets. 
   If only FRAME is given, returns the list of FRAME's slots."
  (cond (value (FramePut frame slot facet value))
	(facet (FrameGet frame slot facet))
	(slot  (Facets frame slot))
	(frame (Slots frame))))

;;; ********************************
;;; Path Related Functions *********
;;; ********************************
;;; Path Manipulation

;;; Use immediate-progeny in all the functions below?
(defun Immediate-Progeny (frame paths)
  "Returns the children of FRAME along the specified PATHS. PATHS
   can be either a list of possible paths, or a single path."
  (if (listp paths)
      (let ((children nil))
	(dolist (path paths children)
	  (setq children
		(append children
			(frameget frame path :value)))))
    (frameget frame paths :value)))

(defun FrameGetClasses (frame &optional (path :AKO))
  "Returns a list of the classes of a frame."
  ;; Closure-set is the list of classes if path(slot) is :ako.
  (transitive-closure frame path))

(defun Transitive-Closure (frame &optional (slot :AKO) (facet :VALUE))
  "Finds the transitive closure of FRAME by following paths specified
   by SLOT/FACET by traversing the paths in a breadth-first manner.
   Returns the set of all frames found without duplicates. Checks to
   see if a frame has already been visited before proceeding, to
   prevent infinite loops when cycles are encountered."
  ;; In this function, the VISITED list also functions as the closure
  ;; set, since it is the list of all nodes encountered.
  ;; If slot (path) is :AKO, the closure set is the list of classes.
  (do-queue ((node queue progeny 
		   visited)		; to avoid cycles
	     (list frame)		; initial queue
	     ;; Get children of a node.
	     (FrameGet node slot facet)
	     ;; Dequeue
	     (pop queue)
	     ;; Merge: This is breadth-first search.
	     (setf queue (append queue progeny)) 
	     (reverse visited))		; result
    ))

(defun Leaves (frame &optional (slot :KINDSOF) (facet :VALUE))
  "Finds the leaf nodes (buds) of the tree rooted at FRAME by descending
   SLOT/FACET paths by traversing the paths in a breadth-first manner.
   Returns the set of all frames found without duplicates.
   Checks to see if a frame has already been visited before proceeding,
   to prevent infinite loops when cycles are encountered."
  (let ((leaves nil))			; frame slot facet
    (do-queue ((node queue progeny 
		     visited)		; to avoid cycles
	       (list frame)		; initial queue
	       ;; Get children of a node.
	       (FrameGet node slot facet)
	       ;; Dequeue
	       (pop queue)
	       ;; Merge: This is breadth-first search.
	       ;; Old leaves function was depth-first.
	       (setf queue (append queue progeny)) 
	       (reverse leaves))	; result
      (unless progeny
	;; If there are no progeny, it's a leaf.
	(push node leaves)))))

(defun Progeny (frame &optional (slot :KINDSOF) (facet :VALUE))
  "Finds the progeny of FRAME by following SLOT/FACET paths by
   traversing the paths in a breadth-first manner. Returns the
   set of all frames found without duplicates. Checks to see if
   a frame has already been visited before proceeding,
   to prevent infinite loops when cycles are encountered."
  ;; was getall. this one includes the start node.
  (do-queue ((node queue progeny 
		   visited)		; to avoid cycles
	     (list frame)		; initial queue
	     ;; Get children of a node.
	     (FrameGet node slot facet)
	     ;; Dequeue
	     (pop queue)
	     ;; Merge: This is depth-first search.
	     ;; Old function was breadth-first.
	     (setf queue (append progeny queue)) 
	     visited)			; result
    ))

(defun Kill-Path (frame &optional (slot :KINDSOF) (facet :VALUE))
  "Kills FRAME and all of its progeny by following SLOT/FACET paths
   by traversing the paths in a breadth-first manner. As each object
   is destroyed, inverse slot relationships are maintained by
   calling appropriate removal demons. This function is intended for
   the destruction of temporary objects. Frame kernel objects are
   protected against Kill-Path.
   Returns the set of all frames found without duplicates.
   Checks to see if a frame has already been visited before proceeding,
   to prevent infinite loops when cycles are encountered."
  (do-queue ((node queue progeny)	; no need to avoid cycles
	     (list frame)		; initial queue
	     ;; Get children of a node.
	     (FrameGet node slot facet)
	     ;; Dequeue
	     (pop queue)
	     nil)			; progeny handled later
    ;; Protect system defined frames from being deleted.
    (unless (member node *system-frames*)
      ;; Merge: This is breadth-first search.
      ;; Old function was depth-first.
      (setf queue (append queue progeny))
      ;; Note that the frame must be killed *after* the progeny have
      ;; been gotten, since Kill-Frame removes the path as well.
      (Kill-Frame node))))

;;; ****************************************************************
;;; Special Inheritance ********************************************
;;; ****************************************************************

;;; ********************************
;;; Frame Environment **************
;;; ********************************

;;; Global variables used by the Frame Environment.
(defvar %frame nil
  "Global variable containing frame environment's frame arg
   for use by demons.")
(defvar %slot nil
  "Global variable containing frame environment's slot arg
   for use by demons.")
(defvar %facet nil
  "Global variable containing frame environment's facet arg
   for use by demons.")
(defvar %value nil
  "Global variable containing frame environment's value arg
   for use by demons.")
(defvar %other-args nil
  "Global variable containing frame environment's other args
   for use by demons.")

(defvar *values-modes*
  '((:first     . some)
    (:no-values . mapc)
    (:append    . mapcan)
    (:collect   . mapcar))
  "Global variable containing all methods frame-eval may use
   to collect values from demon invocation.")

(defun Frame-Eval (demons values-mode 
			  frame slot facet
			  &optional value other-args)
  "Binds %frame, %slot, %facet, %value and %other-args in the 
   Frame Environment to the supplied values, and then runs
   the demons, returning the result as specified by the values mode.
   Possible values-modes include :FIRST, :NO-VALUES, :APPEND, and :COLLECT.
   Demons is a list of demons, which are forms to be evaluated in
   the frame environment."
  ;; Note that the demons are called on the original frame and not
  ;; the frame containing the demons. Thus methods get run on the original
  ;; instance frame, not the class frame.
  ;; Install the values in the global frame environment.
  (let ((%frame frame)
	(%slot slot)
	(%facet facet)
	(%value value)
	(%other-args other-args))
    (declare (special %frame %slot %facet %value %other-args))
    (when demons
      (funcall (or (cdr (assoc (or values-mode :append) *values-modes*))
		   (error "Unknown values collection mode, ~S." values-mode))
	       #'(lambda (x) 
		   ;; If it's an atom, return it. Otherwise, consider
		   ;; it a form to be evaluated.
		   ;; This allows us to include (@ frame slot facet)
		   ;; as a value of a frame to point to data in another
		   ;; frame.
		   (if (atom x)
		       x
		       ;; If we don't want to eval, we could have a closure
		       ;; and funcall it. That seems preferable, since
		       ;; the closure could be compiled.
		       ;; Note that eval looks in the global environment,
		       ;; but that works here because %frame, %slot, etc.,
		       ;; are all global variables.
		       (eval x)))
	       demons))))

;;; ********************************
;;; Demons *************************
;;; ********************************

;;; Demons are functions that are activated automatically in response to the
;;; need for a value, or when a value is placed or removed. 
;;; Most demons are implemented as facet monitors, although there could
;;; be frame and slot monitors. The facet, as an object, decides whether
;;; the demon should be invoked. 
;;; Demons may use the following frame environment variables:
;;;    %frame %slot %facet %value %other-args

;;; In FrameWork, a method is just a special kind of demon.

;;; Optional arg to specify which demons should be run?

(defun Demon-P (demon)
  "Returns T if the frame is a demon."
  ;; is this really how we want to define demons?
  (member :demon (frameget demon :ako :value)))


(defmacro Define-Demon ((demon-frame 
			 &optional (demon-slot :demon) (demon-facet :value))
			&body body)
  "Macro for defining a new demon. The first argument is the name of the
   demon (i.e., where it is stored) followed by the body of the definition.
   The name is of the form (demon-frame demon-slot demon-facet), where
   demon-frame is the main name of the demon and the slot and facet
   further characterize the demon's actions. Demons have access to the
   frame environment, which consists of the global variables 
   %frame %slot %facet %value of the calling frame and %other-args. "
  ;; used mostly to define facet style demons
  `(progn
     ;; make demon-frame :AKO demon
     ;; Since frameput depends on demons for inverse slot maintenance,
     ;; and the demons haven't been defined yet (bootstrapping problem),
     ;; we hard code the inverses here.
     (frameput-internal ',demon-frame :ako :value :demon)
     (frameput-internal :demon :kindsof :value ',demon-frame)
     ;; install the demon
     ;; Demons are values that are forms. When the demon
     ;; is invoked, the forms are evaluated in the frame environment
     ;; within an implicit progn.
     (frameput-internal ',demon-frame ',demon-slot ',demon-facet
	;; perhaps we should use a closure here instead?
	'(progn ,@body))))

(defun Run-Demon (demon-frame 
		    &optional (demon-slot :demon) (demon-facet :value)
		    (values-mode :append)
		    frame slot facet value other-args)
  "Retrieves the demon definition and evaluates it in the frame 
   environment using frame-eval. Values-mode specifies how values
   are returned: no-values, append, collect, or just the first value."
  (let ((demons (frameget demon-frame
			  (or demon-slot :demon)
			  (or demon-facet :value)
			  :no-demons)))
    (frame-eval demons values-mode
		frame slot facet value other-args)))

;;; ********************************
;;; FrameGet-Z *********************
;;; ********************************
;;; demons currently can't return multiple values. need to modify
;;; frame-eval and frameget-z so that multiple-value returning works.

;;; old frameget-z was like 
;;; (frameget-z frame slot facet :legal-demons '(:value :default :if-needed))

(defvar *cache-values* nil
  "If T, the result of FrameGet-Z demon invocation is cached in the VALUE
   slot of the calling frame.")

;;; Global methods are done by making everything eventually a subclass
;;; of THING and putting global methods/demons on :THING.

;;; specify: whether to evaluate data or not,
;;;     chase indirection pointers or not, to inherit or not,
;;;     what kind of inheritance, what demons should be run....

;;; do we really need the legal-demons arg???
(defun FrameGet-Z (frame slot facet 
			 &key legal-demons
			 (path :AKO) (path-facet :value) 
			 path-focus ancestors-focus
			 args (cache-values *cache-values*)
			 (values-mode :append))
  "Returns the same list as FrameGet, unless the frame object has
   no slot-facet values, in which case a breadth-first search
   is performed along the path relation from the frame until
   such values are found. This enables slot values to be inherited
   through network links. Information which is common to many objects
   may be stored in a common ancestor (instead of redundantly storing
   it in each object) and inherited by its progeny. Also value-returns
   the unexplored queue.

   LEGAL-DEMONS is a list of demons to try if the facet has no value.
   For example, if we want to definitely check :DEFAULT and :IF-NEEDED demons,
   instead of relying on frameget's demon invocation, specify LEGAL-DEMONS
   as '(:DEFAULT :IF-NEEDED).

   Path-focus is an extra path tried for the first frame. This is useful for
   methods, where the first frame could be an instance of a class instead
   of a class. Ancestors-focus is a list of ancestors to be focused upon
   instead of starting the search at the frame -- this is useful in method
   invocation where we sometimes want to consider only a specific set of
   ancestors of the frame.

   If cache-values is T, values from FrameGet-Z invocation are cached
   in the :VALUE facet of the slot.
   
   Values-mode specifies how the values of demon invocation should be
   returned."
  ;; where to run :before and :after methods? or whether to?
  ;; is legal-demons really necessary?
  (unless (listp legal-demons) (setf legal-demons (list legal-demons)))
  (do-queue ((node queue progeny 
		   visited)		; to avoid cycles
	     (or ancestors-focus
		 (list frame))		; initial queue
	     ;; Get children of a node.
	     (or (when path-focus
		   (prog1
		       (frameget node path-focus path-facet)
		     (setq path-focus nil)))
		 (FrameGet node path path-facet))
	     ;; Dequeue
	     (pop queue)
	     ;; Merge: This is breadth-first search.
	     (setf queue (append queue progeny))
	     nil)
    (let ((result (FrameGet-Z-local node slot facet legal-demons args
				    cache-values values-mode)))
      (when result
	(return (values result
			queue))))))

;;; would be nice to replace this definition with just the body of
;;; the dolist, and trash the dfacets crap.
(defun FrameGet-Z-local (frame slot facet dfacets &optional args
			       (cache-values *cache-values*)
			       (values-mode :append))
  "Returns the value of the first facet or demon-facet that has a value."
  ;; arg to specify whether demons are executed/evaluated or just returned?
  ;; need to unify having values returned with executing procedures to
  ;; return values.
  (let ((result nil))
    (dolist (dfacet (cons facet dfacets))
      (when (setq result
		  (or (cond ((demon-p dfacet)
			     (Run-Demon dfacet :demon :value values-mode
					frame slot dfacet nil args))
			    ((listp dfacet)
			     (Run-Demon (first dfacet)
					(second dfacet)
					(third dfacet)
					values-mode
					frame slot dfacet nil args)))
		      (frameget frame slot dfacet)))
	(when cache-values 
	  (frameput frame slot :value result))
	(return result)))))

;;; ********************************
;;; Classes, Instances, and Methods 
;;; ********************************

;;; &key instead of &optional ?
(defun Is (node supernode &optional (PATH :AKO) (BlockCats nil) visited)
  "Returns non-NIL if, following path links, node is a descendent of
   supernode if supernode is an atom, or if node is a member of supernode 
   if supernode is a list. The search along path will ignore blockcats."
  ;; visited is to catch cycles
  (when (and node 
	     (not (member node BlockCats))
	     (not (member node visited)))
    (if (eqmemb node Supernode :test #'eq) 
	node
      (dolist (child (FrameGet node PATH :VALUE) nil)
	(let ((temp (is child supernode path blockcats (cons node visited))))
	  (when temp (return temp)))))))

(defun class-p (node)
  "Tests to see if its argument is a class."
  (member :class (frameget node :type :value)))

(defun superclasses (node)
  "Returns the superclasses of a node."
  (frameget node :AKO :value))

(defsetf superclasses (node) (value)
  `(frameput ,node :AKO :value ,value))

(defun subclasses (node)
  "Returns the subclasses of a node."
  (frameget node :kindsof :value))
(defsetf subclasses (node) (value)
  `(frameput ,node :kindsof :value ,value))

(defmacro defclass (name superclasses &rest slots)
  "Defines a new class with the specified name, superclasses and slots.
   Superclasses defaults to (THING) if not given by the user, so that
   the class hierarchy is rooted at THING."
  `(progn
     ;; declare it's type to be CLASS
     (frameput ',name :type :value :class)
     ;; make it a subclass of the superclasses
     ,@(mapcar #'(lambda (superclass) 
		   `(setf (superclasses ',name) ',superclass))
	       (or superclasses
		   ;; default superclass is :THING
		   '(:thing)))
     ;; set up the slots
;     ,@(mapcar #'(lambda (slot)
;		   `(frameput ',name ',(first slot) 'value ',(second slot)))
;	       slots)
     ;; Nick: do a frameput for all the facets of each slot
     ,@(mapcan #'(lambda (slot)
		   (mapcar #'(lambda (facet)
			       `(frameput ',name ',(first slot)
					  ',(car facet)
					  ;; cadr and not cdr because
					  ;; there's only one value. If we
					  ;; want it to be several forms,
					  ;; will need to use an explicit
					  ;; PROGN there.
					  ',(cadr facet)))
			   (cdr slot)))
	       slots)
     ;; Return the name of the class.
     ',name))

(defun subclass-p (node &optional (superclass :THING))
  "Tests to see if its argument is a subclass of superclass, which defaults
   to the root class."
  (is node superclass :ako))

(defun superclass-p (node &optional subclass)
  "Tests to see if its argument is a superclass of subclass, which defaults
   to nil."
  (is node subclass :kindsof))

(defun instance-of (node)
  "Returns the CLASS of a node."
  (frameget node :CLASS :value))
(defsetf instance-of (node) (class)
  `(frameput ,node :CLASS :value ,class))

(defun instance-p (node)
  "Tests to see if its argument is an instance, but doesn't care of what
   frame it is an instance."
  (not (null (instance-of node))))

(defun instances (node)
  "Returns the instances of a node."
  (frameget node :instances :value))

(defun Is-A-P (node supernode)
  "Tests to see if NODE is a SUPERNODE by searching the class hierarchy.
   Will traverse one CLASS link at the start of the search to correctly
   process leaf instances, and then continues with :AKO links. Returns the
   type of link (:CLASS or :AKO) or NIL."
  (or (when (is (frameget node :CLASS :value) supernode :AKO) 
	:CLASS)
      (when (is node supernode :AKO)
	:AKO)))


;;; for make-instance

(defmacro Instance-Name (type)
  "Generates a new symbol, given the basic name of the frame.
   This is used to guarrantee a unique frame name by adding a 
   numerical suffix to the name."
  `(gensym (symbol-name ,type)))
;  `(gentemp (symbol-name ,type)))


(defun merge-heritage (frame class &key (path :ako) (path-facets '(:value))
			     slots-to-ignore)
  "Merges the structure pointed to by the FRAME with all the
   corresponding structures of the frames accessible along the :AKO
   link. SLOTS-TO-IGNORE is a list of the slots which shouldn't be
   merged. Values are appended."
  ;; should we record the source frame for each slot?
  (pushnew path slots-to-ignore)
  (do-queue ((node queue progeny 
		   visited)		; to avoid cycles
	     (list class)		; initial queue
	     ;; Get children of a node.
	     (FrameGet node path :value) ; was path-facet, changed by nick
	     ;; Dequeue
	     (pop queue)
	     ;; Merge: This is breadth-first search.
	     (setf queue (append queue progeny))
	     frame)
    (dolist (slot (set-difference (slotnames node) slots-to-ignore))
      (dolist (facet path-facets)
	(dolist (value (frameget node slot facet)) ; was 'value --nick
	  (frameput frame slot facet value)))))) ; was 'value --nick


(defun Make-Instance (class &rest slot-values-list)
  "Generates a new instance of the class: Creates a name for the instance,
   a frame for the name, and links that frame to the class via a CLASS link.
   Copies the default slot values inherited from the class hierarchy into 
   the instance and then initializes the supplied slot values.
   Class, slotnames, and slot values must all be quoted. For example,
   (make-instance 'elephant 'name \"Clyde\".
   Returns the name of the instance."
  ;; Use keywords for slots?
  ;; run make methods for instance's class (have defaults on THING class).
  ;; i.e., put the slot initialization and such in the make method?
  (let ((new (instance-name class)))
    (merge-heritage new class :path :ako 
		    ;; make instances inherit demons --nick
		    :path-facets '(:if-added :value :if-needed)
		    :slots-to-ignore (let ((result nil))
				       ;; ignore any slot which is 
				       ;; to be initialized
				       (do* ((svl slot-values-list (cddr svl))
					     (slot (car svl) (car svl)))
					   ((null svl) 
					    (cons :CLASS result))
					 (push slot result))))
    (initialize-slots new slot-values-list)
    (setf (instance-of new) class)    
    new))

(defun initialize-slots (frame slot-values-list)
  "Initializes the values of the specified slots in frame, installing
   them in the :value facet. Slot-values-list is a list of alternating
   slot names and values."
  (do* ((svl slot-values-list (cddr svl))
	(slot (car svl) (car svl))
	(value (cadr svl) (cadr svl)))
      ((null svl)
       frame)
    (frameput frame slot :value value))) 

;;; Stolen from PCL:
(eval-when (compile load eval)
(defun extract-declarations (body &optional environment)
  "Extracts the documentation string and declarations from a function body."
  (declare (values documentation declarations body))
  (let (documentation declarations form)
    (when (and (stringp (car body))
               (cdr body))
      (setq documentation (pop body)))
    (block outer
	   (loop
	    (when (null body) (return-from outer nil))
	    (setq form (car body))
	    (when (block inner
			 (loop (cond ((not (listp form))
				      (return-from outer nil))
				     ((and (symbolp (car form))
					   (string-equal
					    (symbol-name (car form))
					    "DECLARE"))
				      ;; was (eq (car form) 'declare)
				      (return-from inner 't))
				     (t
				      (multiple-value-bind (newform macrop)
					  (macroexpand-1 form environment)
					(if (or (not (eq newform form)) macrop)
					    (setq form newform)
					  (return-from outer nil)))))))
	      (pop body)
	      (dolist (declaration (cdr form))
		(push declaration declarations)))))
    (values documentation
            (and declarations `((declare ,.(nreverse declarations))))
            body)))
)


(defmacro defmethod ((message-name frame &optional (mode :method))
		     arglist
		     &body body)
  "Defines a method for message MESSAGE-NAME for the FRAME object.
   Mode is either :METHOD, :BEFORE or :AFTER, for regular methods, before
   and after methods."
  ;; NOTE: methods do *not* have access to the frame environment????
  ;; what about %frame?
  ;; method combination: where is method placed in list of methods by frameput?
  ;; defaults to being placed at the end of the list. should we provide
  ;; for putting it at the front? also, the other aspect of method
  ;; combination is control over the search, which we have to take
  ;; care of in frameget-z.
  ;; (message frame :method)
  ;; (message frame :before)
  ;; (message frame :after)
  (multiple-value-bind (documentation declarations body)
      (extract-declarations body)
    `(frameput ',frame ',message-name ',mode
	       #'(lambda ,arglist
		   ,@(when documentation (list documentation))
		   ,@declarations
		   (declare (special %frame))
		   ,@(case mode
		       (:method body)
		       (:after `((call-next-method) ,@body))
		       (:before `(,@body (call-next-method))))))))

(defvar *ancestors-queue* nil
  "Global variable accessible to methods that contains a list that
   represents the state of the queue in FrameGet-Z when this method
   was found.")

(defvar *calling-frame* nil
  "Global variable accessible to methods that contains the name of
   the frame to which the message was sent.")

(defvar *message-name* nil
  "The name of the current message being processed.")

(defvar *message-arguments* nil
  "The list of arguments of the current message being processed.")

(defvar *method-type* :method
  "The type of method currently being applied (:method, :before, 
   or :after).")

;;; for call-next-method to inherit properly, I think we want to save
;;; the entire search-queue from frameget-z, and not just the current
;;; node. The latter leads to a dfs-like search, where the former
;;; would remain bfs. for demons, the latter results in just the fringe.

(defmacro call-next-method ()
  "Calls the next method up in the calling hierarchy for this frame."
  `(when (and *ancestors-queue* *message-name* *calling-frame* *method-type*)
     (run-methods *calling-frame* *message-name* *message-arguments*
		  *method-type* *ancestors-queue*)))

;;; :BEFORE and :AFTER methods need to be run outside in and inside out,
;;; respectively. We accomplish this in SEND in a neat way: we call the
;;; :BEFORE method of the frame, then the regular methods, and then
;;; the :AFTER methods, finally returning the values from the regular
;;; methods. Within the definition of :BEFORE methods, the last thing
;;; they do (before returning their values, which aren't used anyway)
;;; is run CALL-NEXT-METHOD. The :AFTER methods behave similarly, but
;;; run CALL-NEXT-METHOD first, before the rest of the body of the
;;; method. Defmethod installs the (CALL-NEXT-METHOD) form in the
;;; appropriate place automagically. Thus the regular methods are
;;; inherited in a breadth-first manner and all the :BEFORE and :AFTER
;;; methods are always run. The :BEFORE/:AFTER methods also get run
;;; in the appropriate inheritance order, even when a class has
;;; multiple parents.

(defun SEND (frame message &rest args)
  "Sends a message to the frame, and receives method(s) from the frame
   for dealing with the message. Executes the methods in the frame
   environment of the calling frame, along with any supplied arguments."
  (run-methods frame message args :before nil)
  (multiple-value-prog1 
      (run-methods frame message args :method nil)
    (run-methods frame message args :after nil)))

(defun run-methods (frame message args &optional (type :method) ancestors)
  "Sends MESSAGE to FRAME, retrieving any methods of the proper TYPE (:METHOD,
   :AFTER, or :BEFORE). Calls the methods on the ARGS. If ANCESTORS is 
   supplied, it is used as the focus for where to begin searching for
   methods."
  ;; Note: the args are for the method itself, not method lookup. That's
  ;; why we don't pass them to frameget-z. Makes us think that
  ;; demons, frame-eval and frameget-z don't need this %other-args crap.
  (let ((%frame frame))
    (declare (special %frame))
    ;; binds %frame to the current frame, instead of passing it explicitly
    ;; as an argument to the method.
    (multiple-value-bind (methods queue)
	(FrameGet-Z frame message type
		    ;; since it's an instance, we first
		    ;; get its class before climbing the class
		    ;; hierarchy.
		    :path-focus (unless ancestors :class)
		    ;; for call-next-method we need to specify
		    ;; from where the search should continue. 
		    ;; This pops up to the state of the queue
		    ;; as value-returned by frameget-z.
		    :ancestors-focus ancestors
		    :values-mode :first)
      ;; Methods is a list of the form (<method-frame> <methods>).
      ;; Note that frameget-z just returns the methods and doesn't execute
      ;; them. Here is where we execute them -- and we execute them on the
      ;; original calling frame.
      (if methods
	  (let ((*ancestors-queue* queue) ; extract from methods.
		(*calling-frame* frame)
		(*message-name* message)
		(*message-arguments* args))
	    ;; frame message :method nil
	    (funcall (cdr (assoc :append *values-modes*))
		     #'(lambda (x)
			 ;; if x isn't a function, just return it.
			 ;; do we need this to merge executing methods with 
			 ;; getting values (possibly cached) from slots?
			 (if (functionp x)
			     ;; the arg used to be (list* frame args).
			     ;; instead of passing the frame explicitly
			     ;; as an argument to the method, we bind
			     ;; %frame to the frame so that it may be
			     ;; used within the method. Need to be
			     ;; careful to prevent %frame from being
			     ;; bound in the closure.
			     ;; Perhaps we should modify defmethod to always
			     ;; prepend 'self to the arglist, so that it
			     ;; can access itself?
			     (apply x args) 
			     x))
		     ;; was (second methods)
		     methods)) 
	  (unless ancestors
	    ;; Print error message unless we're searching for ancestor methods
	    (format t "~&~A does not have a known ~A method for ~A"
		    frame type message))))))

;;; ********************************
;;; Saving Frames ******************
;;; ********************************
;;; Function for saving all defined frames to a file. Doesn't work well
;;; with compiled demons. Maybe we should have a separate store of all demon
;;; definition forms?
;;; To restore, just load the file.
;;; To erase all user defined frames, do (delete-frames) first.

(defun Save-Frames (&optional (filename "output.fwk") (frames *frames*))
  "Pretty prints the frames created by FrameWork into a file. The frames
   are both human readable and lisp readable (so that loading the file
   restores the frames into lisp)."
  (format *standard-output* "~&Saving frames to file (~A)." filename)
  (with-open-file (stream filename :direction :output :if-exists :supersede)
    ;; need to print out a commented header here  (frames saved at TIME)
    ;; which lists time, date, user who saved, list of frame names saved.
    (framework-herald stream)
    (terpri stream)
;    (format stream "~%(in-package \"FW\")~%")
    (dolist (frame frames)
      (save-frame frame :stream stream)))
  *frames*)

(defun Save-Frame (frame &key (stream *standard-output*))
  ;; (print `(def-frame ',frame ',(frame frame)) stream)
  (cond ((framep frame)
	 (format stream "~%(DEF-FRAME ~A" frame)
	 (pprint-frame frame stream :readable t :indent 3)
	 (format stream ")~%"))
	(t (format *error-output* "save-frame: ~A has no frame definition!"
		   frame))))

;;; ********************************
;;; Pretty Printer *****************
;;; ********************************
(defvar *default-ppframe-indent* 3
  "Indentation factor: amount the indent is increased 
   at each additional level.")

(defun PPF (frame &optional (stream *standard-output*) 
		  &key (readable t) (indent 0))
  "A synonym for pprint-frame."
  (pprint-frame frame stream :readable readable :indent indent))

(defun PPrint-Frame (frame &optional (stream *standard-output*) 
			   &key (readable t) (indent 0))
  "If readable is NIL, parentheses are omitted."
  (cond ((framep frame)
	 (pprint-frame-internal (frame frame) stream readable indent))
	(t
	 (format *error-output* "~&pprint-frame: ~A has no frame definition!"
		 frame)
	 (force-output *error-output*)
	 (values))))

(defvar *max-levels* 3
  "Maximum number of levels in a Frame.")
(defun pprint-frame-internal (frame stream &optional (readable t) (indent 0)
				    (level 0))
  (cond ((and level (>= level *max-levels*))
	 (format stream "~%~V,,,' A~A" indent "" frame))
	((consp frame)
	 (format stream "~%~V,,,' A~:[~;(~]~A"
		 indent "" readable 
		 (first frame))
	 (dolist (item (rest frame))
	   (pprint-frame-internal item stream readable
				  (+ indent 
				     *default-ppframe-indent*)
				  (1+ level)))
	 ;(format stream "~:[~;~%~V,,,' A)~]" readable indent "")
	 (format stream "~:[~;)~]" readable)
	 (first frame))
	(t 
	 (format stream "~%~V,,,' A~A" indent "" frame))))

;;; ********************************
;;; FrameWork Listener *************
;;; ********************************
(defvar *framework-prompt* "~%FW> "
  "Prompt used in the FrameWork Listener.")
(defvar *print-frame-bodies* t
  "If the result of a command execution is the name of a frame, the
   frame body will be printed and the name returned.")

(defvar *framework-commands* nil
  "List of defined commands for the listener.")

(defstruct (framework-command (:type list))
  name
  short-doc
  long-doc
  function)

(defmacro define-fw-listener-command (name arg-list short-doc long-doc
					 &body body)
  "Defines a new command for the FrameWork listener. Name is either the
   name of the command, or a list of synonyms. Short-doc is for the
   summary help display. Long-doc is what should be displayed when
   asking for detailed help on the command. If the last form in the
   body is :noprint, the result of evaluating the command is not printed.
   When called from the listener, the rest of the line is received as
   arguments."
  `(progn 
     (setf *framework-commands*
	 (append (delete-command ',name)
		(list (make-framework-command
		       :name ',name
		       :short-doc ,short-doc
		       :long-doc ,long-doc
		       :function #'(lambda ,arg-list ,@body)))))
     ',name))

(defun delete-command (name)
  "Deletes a FrameWork listener command."
  (delete name *framework-commands* 
	  :key #'framework-command-name
	  :test (if (listp name) #'equalp
		  #'eqmemb)))

(defun find-command (name)
  "Finds the FrameWork listener command with that name or nickname."
  (find name *framework-commands* 
	:key #'framework-command-name
	:test #'(lambda (a b) (eqmemb a b :test #'string-equal))))

(define-fw-listener-command (quit q) (&rest ignore)
  "Quit the FrameWork Listener."
  "Exit from the FrameWork Listener."
  (declare (ignore ignore))
  (format *standard-output* "~&Quitting FrameWork Listener.")
  (force-output *standard-output*)
  (throw 'quit-framework nil))

(define-fw-listener-command (help ?) (&optional topic)
  "Get help on using the FrameWork Listener."
  "Type 'help' to get a list of commands. 
   Type 'help <topic>' to get help on a particular topic."
  (cond (topic
	 (let ((command (find-command topic)))
	   (cond (command
		  (format *standard-output* "~&Help on ~A:" topic)
		  (format *standard-output* "~&   ~A"
			  (framework-command-long-doc command)))
		 (t
		  (format *standard-output* "~&Couldn't find help on ~A." 
			  topic)))))
	(t
	 ;; General help
	 (format *standard-output* "~&Help topics available:")
	 (dolist (topic *framework-commands*)
	   (let ((name (framework-command-name topic))
		 (doc  (framework-command-short-doc topic)))
	     (if (listp name)
		 (format *standard-output* "~&   ~{~A~^, ~} ~2,18T- ~A"
		     name doc)
	     (format *standard-output* "~&   ~A ~2,18T- ~A"
		     name doc))
	     (force-output *standard-output*)))
	 (format *standard-output* 
		 "~&Type 'help <topic>' to get help on a particular topic.")))
  :noprint)

(define-fw-listener-command put (frame slot facet value)
  "Add a value to a frame."
  "Adds a VALUE to the FACET facet of the SLOT slot of FRAME."
  ;; extend this to make slot, facet, value all optional.
  (frameput frame slot facet value))

(define-fw-listener-command put! (frame slot facet value)
  "Add a unique value to a frame."
  "Assigns VALUE as the unique value of the FACET facet
   of the SLOT slot of FRAME."
  (frameput! frame slot facet value))

(define-fw-listener-command get (frame &optional slot facet)
  "Get a value from a frame."
  "GET frame slot facet        - runs frameget
   GET frame slot              - runs facets
   GET frame                   - runs slots"
  (cond (facet (frameget frame slot facet))
	(slot (facets frame slot))
	(frame (slots frame))))

(define-fw-listener-command get! (frame slot facet)
  "Gets a unique value from a frame."
  "GET! frame slot facet        - runs frameget!"
  (frameget! frame slot facet))

(define-fw-listener-command kill (frame &optional slot facet value)
  "Removes a value from a frame."
  "KILL frame slot facet value    - runs FrameRemove
   KILL frame slot facet          - runs Kill-Facet
   KILL frame slot                - runs Kill-Slot
   KILL frame                     - runs Kill-Frame"
  ;; remove should really do different things depending on the
  ;; number of args. I.e., remove entire slots and facets.
  (cond (value
	 (frameremove frame slot facet value))
	(facet
	 (Kill-Facet frame slot facet))
	(slot
	 (Kill-Slot frame slot))
	(frame
	 (Kill-Frame frame))))

(define-fw-listener-command save (&optional filename &rest frames)
  "Saves frames to a file."
  "Saves frames to a file. To use, type
      SAVE <filename> <f1> <f2> ...
   If frames are not specified, defaults to all frames."
  (cond (frames
	 (save-frames filename frames))
	(filename
	 (save-frames filename))
	(t
	 (save-frames))))

(define-fw-listener-command restore (filename)
  "Restores frames from file."
  "Restores frames from a file by loading it. To use, type
      RESTORE <filename>"
  (load filename))

(define-fw-listener-command dribble (&optional filename
					       &key (if-exists :append))
  "Dribbles output to a file."
  "Dribbles output to a specified file. To begin dribbling, type
     DRIBBLE <filename>
   To stop dribbling, type
     DRIBBLE"
  ;; Damn. Dribble can't be relied on if not called at top level,
  ;; according to CLtL2. So we give up in disgust and write our 
  ;; own for use here.
  (if filename
      (with-open-file (f filename :direction :output  :if-exists if-exists
                         :if-does-not-exist :create)
        (catch 'dribble-punt
          (let ((*standard-output*
                 (make-broadcast-stream *standard-output* f))
                (*standard-input*
                 (make-echo-stream *standard-input* f)))
	    (listener))))
    (throw 'dribble-punt nil))
  :noprint)

(define-fw-listener-command (<relation> rel) ()
  "Adds a link between two frames."
  "To link two frames with a predefined relation, type
      <relation> <frame1> <frame2> 
   For example,
      :AKO CLYDE ELEPHANT"
  :noprint)

(define-fw-listener-command FRAMES (&optional system-frames)
  "Returns a list of all defined frames."
  "Returns a list of all defined frames. If given an argument,
   returns a list of all defined system frames."
  (if system-frames
      *system-frames*
    *frames*))

(defun listify-string (string)
  "Turns a string into a list of symbols."
  (let ((eof (gensym))
	(result nil)
	(start 0)
	item)
    (loop
     (multiple-value-setq (item start)
	 (read-from-string string nil eof :start start))
     (when (eq item eof)
       (return result))
     (setq result (nconc result (list item))))))

(defvar *schedule* nil
  "A list of actions which are executed once every tick of the clock.
   They must have bounded execution time.")

(defun get-input (&optional (stream *standard-input*))
  "Gets input from the user. If the user isn't typing anything, runs
   any functions found on the *schedule*."
  (loop
   (when (listen stream)
     (return (read-line stream)))
   (when *schedule*
     (dolist (item *schedule*)
       (funcall item)))))

(defun listener ()
  "A READ-EVAL-PRINT loop for convenient interaction with FrameWork and
   demoing the system. Interprets framework commands in abbreviated form,
   without parentheses and quotes. Typing the name of a frame will display
   it pretty printed. Frames created using the listener are accessible
   to the save-frame utility."
  (catch 'quit-framework
    (framework-herald)
    (format *standard-output* "~%  (For help, type 'help' or '?')")
    ;; Your basic read-eval-print loop.
    (loop
     ;; Prompt the user.
     (format *standard-output* *framework-prompt*) 
     (force-output *standard-output*)
     ;; Read in a line, listifying it.
     (let ((command (listify-string (get-input))))
       ;; change this to a multiple-value-bind of (result print)
       ;; where print can be :noprint or :notframe...
       (let ((result (framework-eval command)))
	 (when command
	   (setq +++ ++
		 ++ +
		 + command))
	 (unless (eq result :noprint)
	   (setq *** **
		 ** *
		 * result)
	   (if (and *print-frame-bodies* (framep result))
	       (pprint-frame result);; pretty print frame
	     (pprint result))))))))

;;; catch evaluation errors so that we don't go into the debugger.
(defun Framework-Eval (line)
  "Evaluates commands typed to the framework listener by the user.
   If the line begins with a symbol, and that symbol represents a
   framework listener command, the apropriate command is called
   with the rest of the line as input. If the symbol is the name
   of a frame, it is pretty printed. Otherwise the line is treated
   like a regular lisp form."
  ;; in put/get/... no need to put quotes in front of frame/slot/facet..
  ;; however, it will still eval non symbols. ??? 
  (let* ((key (first line))
	 (command (when (or (atom key) (stringp key))
		    (find-command key))))
    (cond (command
	   (apply (framework-command-function command)
		  (rest line)))
	  ((and (framep key)
		(is-a-p key :relation) ; relation is a kind of slot
		(= 3 (length line)))
	   ;; RELATION f1 f2: adds a link between f1 and f2.
	   (frameput (second line) key :value (third line))
	   )
	  ((framep key)
	   ;; pass it through to pretty print it
	   (if (rest line)
	       ;; if more than just the frame name, call @ on it.
	       ;; thus typing <frame> <slot> prints out a list of the facets...
	       (apply #'@ line)
	     key))
	  ((and (functionp key)
		(fboundp key)
		(not (null (rest line))))
	   ;; assume it is lisp, and will eval correctly
	   ;; a function or a lambda
	   (eval line))
	  ((or (listp key)(and (symbolp key)(boundp key)))
	   (eval key))
	  (t
	   ;; error
	   (format *standard-output* "~%ERROR: Unknown command or form ~A"
		   line)
	   :noprint))))

;;; ********************************
;;; Graphics ***********************
;;; ********************************
(defun explode (symbol)
  (map 'list #'identity (symbol-name symbol)))
(defun implode (list)
  (intern (map 'string #'identity list)))
(defun crush (a b)
  (implode (append (explode a) (explode b))))

(defvar *properties-are-symbols* nil
  "If T, properties are represented as P and ~P. 
   If NIL, properties are represented as P and (NOT P).")

(defun Negate (property)
  "Forms the negation of property."
  (if *properties-are-symbols*
      (let ((chars (explode property)))
	(if (char= (first chars) #\~)
	    (implode (cdr chars))
	  (implode (cons #\~ chars))))
    (if (car-eq property 'not)
	(second property)
      (list 'not property))))

(defun Has-Property (frame property 
		      &optional (path :ako) (path-facet :value)
		      (property-slot :ako) (property-facet :mode))
  "Checks whether FRAME has the given PROPERTY. Property values are
   stored on the MODE facet of the :AKO slot, and may be inherited
   in a breadth-first manner from ancestors along the :AKO path. The
   inheritance of a given property P may be blocked by the property
   ~P (NOT P) occurring somewhere along the path from FRAME to the ancestor
   with the property P. This provides for inheritance with exceptions."
  (let ((block-property (negate property)))
    (do-queue ((node queue progeny 
		     visited)		; to avoid cycles
	       (list frame)		; initial queue
	       ;; Get children of a node.
	       (FrameGet node path path-facet)
	       ;; Dequeue
	       (pop queue)
	       nil			; progeny handled separately
	       nil)			; result
      (let ((properties (frameget node property-slot property-facet)))
	(cond ((member property properties :test #'equalp)
	       ;; It has the property, so return successfully
	       (return node))
	      ((not (member block-property properties :test #'equalp))
	       ;; Only continue searching this node's ancestors if
	       ;; it isn't blocked.
	       ;; Merge: This is breadth-first search.
	       (setf queue (append queue progeny))))))))

(defun Tree-Path (frame paths &optional (restrict nil)(show-frame nil)
		       (visited nil))
  "Constructs a tree from FRAME's inheritance along PATHS, suitable
   for displaying using a graphing function. The resulting tree is
   of the form (root subtree1 subtree2 ...) where each subtree is 
   of the same form. If SHOW-FRAME is T, includes the actual frame
   structure of the leaves. RESTRICT is either a maximum depth, 
   a property, or a function of the form (FUNCALL <function> . <args>).
   If RESTRICT is a property, only nodes with that property are shown,
   with intermediate nodes visible, of course."
  (let (children)
    (cond ((member frame visited :test #'equal) 
	   ;; If we've already seen this frame along the path, we've
	   ;; hit a cycle. So stop expanding the tree, and indicate
	   ;; truncation with an @-sign prepended to the frame name.
	   ;; (Also signifies indirection.)
	   ; (implode (cons #\@ (explode frame)))
	   (cons '@ frame))
	  ((and (or (not (numberp restrict)) (plusp restrict))
		(setq children (immediate-progeny frame paths)))
	   ;; it isn't the fringe
	   (let ((branches nil)
		 (branch nil)
		 (new-restrict (if (numberp restrict) (1- restrict) restrict)))
	     (push frame visited)
	     (dolist (child children)
	       (setq branch (Tree-Path child paths new-restrict 
				      show-frame visited)) 
	       (setq branches
		     (append branches
			     (list 
			      (cond ((null branch) child)
				    ((atom branch) (list branch))
				    (t branch))))))
	     (cons (frame-rep frame restrict branches nil)
		   branches)))
	  (t
	   ;; It's a leaf (either restrict = 0, or no more children).
	   (frame-rep frame restrict nil show-frame)))))

(defun Frame-Rep (frame restrict &optional show-if-fails show-frame) 
  "Creates a representation for the frame as a node in the graph."
  (cond ((or (numberp restrict)
	     (null restrict)
	     (if (car-eq restrict 'funcall)
		 (funcall (cadr restrict) frame (cddr restrict))
	         (Has-Property frame restrict)))
	 (if show-frame
	     ;; If T, shows the entire frame property, not just the name
	     (Tree-Copy (or (Frame frame) frame))    
	   frame))
	(show-if-fails
	 ;; failed the restriction, but we show it anyway because 
	 ;; it is on the path to something that passes the restriction.
	 ; (implode (cons #\! (explode frame)))
	 (cons '! frame))))

(defvar *Show-Parentheses* t
  "If T, shows the parentheses around the values.")

(defun Tree-Copy (tree &optional (keyp t) (show-parens *Show-Parentheses*))
  "Returns a copy of TREE (a frame). If show-parens is T, puts 
   parentheses around the values. This is useful for display them as
   individual nodes of the frame, instead of just a big list."
  (cond ((null tree)
	 (list '*nil))
	((consp tree)
	 ;; assume the car is a key, and everything else not
	 (cons (Tree-Copy (first tree) t show-parens)
	       (let ((result nil))
		 (dolist (branch (rest tree) (nreverse result))
		   (push (Tree-Copy branch nil show-parens) result)))))
	((and show-parens (not keyp))
	 (list tree))
	(t tree)))

#|
;;; Interface to Bates' PostScript Graphing Utility
;(load "/afs/cs/user/mkant/Lisp/PSGraph/psgraph")

(defparameter *postscript-output-directory* "")
(defun Show-Graph (frame paths &key (restrict nil)(show-frame nil)
			 (shrink nil) 
			 (directory *postscript-output-directory*))
  "Creates a postscript file that displays the network starting from FRAME 
   and traversing PATHS."
  (let ((psgraph:*fontsize* 9)
        (psgraph:*second-fontsize* 7)
;       (psgraph:*boxkind* "fill")
        (psgraph:*boxgray* "0")		; .8
        (psgraph:*edgewidth* "1")
        (psgraph:*edgegray* "0"))
    (labels ((stringify (thing)
		(cond ((stringp thing) (string-downcase thing))
		      ((symbolp thing) (string-downcase (symbol-name thing)))
		      ((listp thing) (stringify (car thing)))
		      (t (string thing)))))
	    (let* ((tree (Tree-Path frame paths restrict show-frame))
		   (fname (stringify (car tree)))
		   (filename (concatenate 'string directory
					  (string-trim '(#\: #\|) fname)
					  ".ps")))
	      (format t "~&Creating PostScript file ~S." filename)
	      (with-open-file (*standard-output* filename
						 :direction :output
						 :if-does-not-exist :create
						 :if-exists :supersede)
		(psgraph:psgraph tree
				 #'cdr 
				 #'(lambda (x)
				     (list (stringify (car x))))
				 shrink nil #'eq))))))

|#


;;; ********************************
;;; Slot Paths *********************
;;; ********************************
;;; The following macro character definition and two functions define
;;; a special syntax for extracting the value at the end of a series
;;; of slots. For example, if cat is :AKO mammal and :AKO SIAMESE
;;;    $!cat.ako --> MAMMAL
;;;    $cat.ako  --> (MAMMAL SIAMESE)
;;; The general syntax is $frame.slot1.slot2.slot3...
;;; This is useful for extracting information: $me.office.room-number
;;; Question of whether the first slot should default to the current
;;; frame, to make this really useful in methods.
(eval-when (compile load eval)

  (defvar *path-special-symbols*
      '(demon ako kindsof value default if-needed if-added if-removed
	if-fetched mode 
	put get remove after before method class instances thing
	type types parent child part-of parts is-component-of components)
    "Symbols which should be treated as if they were in the keyword
     package for path reading.")

  (defparameter *framework-readtable* (copy-readtable nil))
  (set-macro-character #\. #'(lambda (stream char)
			       (declare (ignore stream char))
			       nil) 
		       nil
		       *framework-readtable*)

  (defun path-reader (stream char)
    "Reader macro which reads in a special path syntax. For example,
      $!cat.ako --> MAMMAL
      $cat.ako  --> (MAMMAL SIAMESE)."
    (declare (ignore char))
    (let ((*readtable* *framework-readtable*))
      (let ((path-function 'path-get))
	(when (char= (peek-char nil stream nil nil t) #\!)
	  (setq path-function 'path-get!)
	  (read-char stream nil nil t))
	(do ((path (list (read stream t nil t))
		   (cons (progn 
			   (read-char stream nil nil t)
			   (read stream t nil t))
			 path)))
	    ((not (char= (peek-char nil stream nil #\space t) #\.))
	     `(,path-function 
	       ,@(mapcar #'(lambda (x) 
			     (cond ((find (symbol-name x)
					  *path-special-symbols*
					  :key #'symbol-name
					  :test #'string-equal)
				    (intern x "KEYWORD"))
				   (t
				    `(quote ,x))))
			 (nreverse path))))))))

  (set-macro-character #\$ #'path-reader))

(defun path-get! (frame &rest path)
  "Extracts the value at the end of the path beginning at frame
   using frameget!. E.g., (path-get! me 'office 'room-number).
   Here a path is a series of slots."
  (let ((temp frame))
    (dolist (slot path)
      (setq temp (frameget! temp slot :value)))
    temp))

(defun path-get (frame &rest path)
  "Extracts the values at the end of the path beginning at frame
   using frameget. E.g., (path-get me 'office 'room-number).
   Here a path is a series of slots."
  (let ((temp (list frame)))
    (dolist (slot path)
      (let ((temp2 nil))
	(dolist (node temp)
	  (setf temp2 (append temp2 (frameget node slot :value))))
	(setf temp temp2)))
    temp))


;;; ********************************
;;; System Frames ******************
;;; ********************************
;;; These frames define basic relations (slots) and their inverses.

;;; Define freset to remove all frames from the system and 
;;; rebuild the system frames.

;;; DELETE ALL USER AND SYSTEM DEFINED FRAMES:
(delete-frames *frames*)
(delete-frames *system-frames*)

;;; DEFINE THE SYSTEM FRAMES:

;;; The inverse of INVERSE is INVERSE. 
(frameput :inverse :inverse :value :inverse)

;;; Define :AKO/:KINDSOF as inverses (bootstrapping phase).
(frameput :ako :inverse :value :kindsof)

;;; Define RELATION as a kind of SLOT that relates two frames.
(frameput :relation :ako :value :slot)

(defun Define-Inverse-Slots (slot1 slot2)
  "Defines two slots as slots and inverses of each other."
  ;; define each as slots
  (frameput slot1 :ako :value :relation)
  (frameput slot2 :ako :value :relation)
  ;; make them inverses of each other
  (frameput slot1 :inverse :value slot2))

;;; Define the following inverses:
;;;    :CLASS/:INSTANCES
;;;    :AKO/:KINDSOF
;;;    :TYPE/:TYPES
;;;    :PARENT/:CHILD
;;;    :PART-OF/:PARTS
;;;    :IS-COMPONENT-OF/:COMPONENTS
;;; The first two define basic class and instance hierarchies.
(define-inverse-slots :class :instances)
(define-inverse-slots :ako :kindsof) ; :AKO stands for "A Kind Of"
(define-inverse-slots :type :types)
(define-inverse-slots :parent :child)
(define-inverse-slots :part-of :parts)
(define-inverse-slots :components :is-component-of)

;;; Alternate definitions of class and instance hierarchies:
;;;     INSTANCE-OF/INSTANCES
;;;     SUPERCLASSES/SUBCLASSES
;;; (define-inverse-slots :instance-of :instances)
;;; (define-inverse-slots :superclasses :subclasses)

;;; Users may define inverse link pairs in the same manner as the 
;;; pairs listed above using the define-inverse-slots function. This
;;; function stores each link as a value of the RELATION object and
;;; lists each link object as the INVERSE of the other. Note that
;;; INVERSE is its own inverse, so the inverse-slot maintenance
;;; assures that each link is the inverse of the other. 

;;; DEFINE THE DEMONS:

;;; [:value :put :after] 
;;;     inverse-slot maintenance
;;;     runs global :if-added demon
;;; [:value :remove :after] 
;;;     inverse-slot maintenance
;;;     runs global :if-removed demon (:if-erased)
;;; [:value :get :after] 
;;;     runs global :if-needed demon (:if-fetched)

(define-demon (:value :put :after) 
  ;; This demon handles inverse slot maintenance inside frameput
  ;; by means of the call
  ;; (run-demon facet :put :after :append frame slot facet value)
  ;; It is run when facet = value. 
  (let ((inv (inv-slot %slot)))
    (when inv
      (frameput-internal %value inv %facet %frame))))

(define-demon (:value :put :after) 
  ;; runs global :if-added demon
  (run-demon :if-added :demon :value :no-values
	     %frame %slot %facet %value %other-args))

(define-demon (:value :remove :after) 
  ;; generic demon for frameremove inverse slot maintenance.
  (let ((inv (inv-slot %slot)))
    (when inv
      (frameremove-internal %value inv %facet %frame))))

(define-demon (:value :remove :after) 
  ;; runs global :if-removed demon
  (run-demon :if-removed :demon :value :no-values
	     %frame %slot %facet %value %other-args))

(define-demon (:value :get :after) 
  ;; runs global :if-needed demon
  (run-demon :if-needed :demon :value :append
	     %frame %slot %facet %value %other-args))

;;; :if-added, :if-removed, and :if-needed global demon definitions
;;; these just run the local demons.
(define-demon (:if-added :demon :value) 
  ;; facet demon to call appropriate local :if-added demons
  (Run-Demon %frame %slot :if-added :append 
	       %frame %slot %facet %value %other-args))

(define-demon (:if-removed :demon :value) 
  ;; facet demon to call appropriate local :if-removed demons
  (Run-Demon %frame %slot :if-removed :append 
	       %frame %slot %facet %value %other-args))

(define-demon (:if-needed :demon :value) 
  ;; facet demon to call appropriate local :if-needed demons
  (Run-Demon %frame %slot :if-needed :append 
	       %frame %slot %facet %value %other-args))

(define-demon (:default :demon :value) 
  ;; facet demon to get default value
  ;; couldn't we just do a (frameget frame slot :default nil nil)
  ;; to return the value of :DEFAULT instead of evaluating the values
  ;; located in the :default slot?
  (Run-Demon %frame %slot :default :append 
	       %frame %slot %facet %value %other-args))

;;; methods, :before and :after methods.
;;; what about wrappers and whoppers?
(define-demon (:method :demon :value) 
    ;; runs demon locating in [FRAME MESSAGE :method :value]
    (frameget %frame %slot :method :no-demons)) 
(define-demon (:method :after :value) 
    ;; runs demon locating in [FRAME MESSAGE :after :value]
    (frameget %frame %slot :after :no-demons))
(define-demon (:method :before :value) 
    ;; runs demon locating in [FRAME MESSAGE :before :value]
    (frameget %frame %slot :before :no-demons))


;;; INSTALL THE SYSTEM FRAMES:

;;; Store the system frames on *system-frames*, resetting *frames* to nil.
;;; This makes the system frames invisible to user deleting and saving
;;; operations, but does not prevent user modification. In fact, user
;;; modification is necessary for addition of demons and methods.
(setf *system-frames* *frames*
      *frames* nil)

;;; *EOF*

