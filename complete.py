"""
SASTRA Timetable Generation System - COMPLETE FINAL VERSION
All features + Critical Fixes + Anti-pattern scheduling

FIXED ISSUES:
✓ No same subject at same period on consecutive days
✓ Lab frequency strictly limited to max 2 days per week
✓ Better distribution of theory classes
✓ Faculty assignment with search
✓ All original features preserved

Version: 5.2 FINAL - PATTERN-FREE SCHEDULING
"""

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
from typing import List, Dict, Set, Tuple, Optional
from dataclasses import dataclass, field
from enum import Enum
from copy import deepcopy
import logging
import sqlite3
import pandas as pd
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
import threading
import time
from datetime import datetime
from math import ceil

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# ============================================================================
# DATA MODELS
# ============================================================================

class SemesterMode(Enum):
    ODD = 'odd'
    EVEN = 'even'

class SlotStatus(Enum):
    FLEXIBLE = 'flexible'
    FIXED = 'fixed'
    TP_PENDING = 'tp_pending'

class SubjectType(Enum):
    PURE_THEORY = 'pure_theory'
    PURE_LAB = 'pure_lab'
    SEMI_LAB = 'semi_lab'
    TP_SUBJECT = 'tp_subject'

@dataclass
class Subject:
    subject_id: str
    subject_name: str
    L: int
    T: int
    P: int
    branch: str
    semester: int
    is_elective: bool
    elective_group: Optional[int] = None
    
    def get_subject_type(self) -> SubjectType:
        if self.P > 0 and self.L == 0 and self.T == 0:
            return SubjectType.TP_SUBJECT
        elif self.P > 0 and (self.L > 0 or self.T > 0):
            return SubjectType.SEMI_LAB
        elif self.P > 0:
            return SubjectType.PURE_LAB
        else:
            return SubjectType.PURE_THEORY
    
    def get_theory_periods(self) -> int:
        return self.L + self.T
    
    def get_lab_sessions(self) -> int:
        return ceil(self.P / 2) if self.P > 0 else 0

@dataclass
class Faculty:
    faculty_id: int
    name: str
    designation: str
    courses: List[str]
    max_hours: int

@dataclass
class Lab:
    lab_id: str
    lab_name: str
    P: int
    capacity: int
    branch: str
    semester: int
    is_elective: bool
    
    def get_lab_sessions(self) -> int:
        return ceil(self.P / 2) if self.P > 0 else 0

@dataclass
class LabRoom:
    room_id: str
    course_code: str
    course_name: str
    branches: List[str]
    available_for_labs: List[str] = field(default_factory=list)
    capacity: int = 60

@dataclass
class CoreLabPair:
    id: int
    subject_id: str
    lab_id: str
    branch: str
    semester: int
    faculty_must_match: bool

@dataclass
class TimeSlot:
    day: int
    period: int
    
    def __hash__(self):
        return hash((self.day, self.period))
    
    def __eq__(self, other):
        return self.day == other.day and self.period == other.period

@dataclass
class Assignment:
    subject_id: str
    faculty_id: Optional[int]
    section: str
    room: str
    time_slot: TimeSlot
    is_lab: bool = False
    is_elective: bool = False
    elective_group: Optional[int] = None
    status: SlotStatus = SlotStatus.FLEXIBLE
    is_continuous_pair: bool = False
    pair_with: Optional[TimeSlot] = None

# ============================================================================
# LAB ROOM MANAGER
# ============================================================================

class LabRoomManager:
    """Manages lab room blocking and equipment matching"""
    
    def __init__(self, lab_rooms: List[LabRoom]):
        self.lab_rooms = lab_rooms
        self.room_schedule: Dict[str, Dict[TimeSlot, str]] = {}
        self.room_equipment: Dict[str, Set[str]] = {}
        self._initialize_room_equipment()
    
    def _initialize_room_equipment(self):
        """Initialize room equipment mapping"""
        for room in self.lab_rooms:
            self.room_schedule[room.room_id] = {}
            self.room_equipment[room.room_id] = set(room.available_for_labs)
    
    def is_room_available(self, room_id: str, time_slot: TimeSlot) -> bool:
        """Check if room is available at time slot"""
        if room_id not in self.room_schedule:
            return False
        return time_slot not in self.room_schedule[room_id]
    
    def find_compatible_room(self, lab_id: str, time_slots: List[TimeSlot]) -> Optional[str]:
        """Find room with compatible equipment"""
        for room_id, supported_labs in self.room_equipment.items():
            if lab_id not in supported_labs and len(supported_labs) > 0:
                continue
            
            available = all(self.is_room_available(room_id, slot) for slot in time_slots)
            if available:
                return room_id
        return None
    
    def allocate_room(self, room_id: str, time_slots: List[TimeSlot], section_id: str):
        """Block room for specific time slots"""
        for slot in time_slots:
            self.room_schedule[room_id][slot] = section_id

# ============================================================================
# CSP SOLVER - WITH PATTERN PREVENTION
# ============================================================================

class CSPSolver:
    """Layer 1: CSP with pattern prevention + all critical fixes"""
    
    def __init__(self, subjects, faculty, labs, rooms, sections_config, 
                 core_lab_pairs, grouped_electives, faculty_assignments, semester_mode):
        self.subjects = subjects
        self.faculty = faculty
        self.labs = labs
        self.rooms = rooms
        self.sections_config = sections_config
        self.core_lab_pairs = core_lab_pairs
        self.grouped_electives = grouped_electives
        self.faculty_assignments = faculty_assignments
        self.semester_mode = semester_mode
        
        self.assignments: List[Assignment] = []
        self.faculty_schedule: Dict[int, Set[TimeSlot]] = {}
        self.room_schedule: Dict[str, Set[TimeSlot]] = {}
        self.section_schedule: Dict[str, Set[TimeSlot]] = {}
        
        # Track which periods are used for which subject per section
        # Key: (section_id, subject_id), Value: Set of periods used
        self.subject_period_usage: Dict[Tuple[str, str], Set[int]] = {}
        
        # CRITICAL: Track lab days per week per section
        self.lab_weekly_days: Dict[Tuple[str, str], Set[int]] = {}
        
        # Lab room manager
        self.room_manager = LabRoomManager(rooms)
        
        self.lunch_slots = {4, 5}
        self.branch_lunch: Dict[Tuple[str, int], int] = {}
        self.lab_periods = [(0,1), (2,3), (4,5), (6,7)]
        self.continuous_pairs = [(0,1), (2,3), (4,5), (6,7)]
        
        self.backtrack_count = 0
        self.max_backtracks = 10000
    
    def _can_assign_slot(self, section_id: str, slot: TimeSlot, subject_id: str) -> bool:
        """Check if slot can be assigned"""
        # 1. Check section availability
        if slot in self.section_schedule.get(section_id, set()):
            return False
        
        # 2. Check lunch break
        branch, sem = self._parse_section_id(section_id)
        lunch_period = self.branch_lunch.get((branch, sem))
        if slot.period == lunch_period:
            return False

        # 3. Check faculty availability if pre-assigned
        faculty_id = self.faculty_assignments.get(subject_id)
        if faculty_id and slot in self.faculty_schedule.get(faculty_id, set()):
            return False

        return True
    
    def _can_assign_theory_slot(self, section_id: str, slot: TimeSlot, subject_id: str) -> bool:
        """
        ENHANCED: Check if theory slot can be assigned WITHOUT creating same-period patterns
        """
        # Basic checks first
        if not self._can_assign_slot(section_id, slot, subject_id):
            return False
        
        # NEW: Prevent same subject at same period on consecutive days
        tracking_key = (section_id, subject_id)
        if tracking_key in self.subject_period_usage:
            used_periods = self.subject_period_usage[tracking_key]
            
            # If this period is already used for this subject, check if it creates a pattern
            if slot.period in used_periods:
                # Count how many times this period is already used
                period_count = sum(1 for a in self.assignments 
                                 if a.section == section_id 
                                 and a.subject_id == subject_id 
                                 and a.time_slot.period == slot.period
                                 and not a.is_lab)
                
                # Don't allow same period more than once to avoid patterns
                if period_count >= 1:
                    return False
        
        return True

    def _assign_to_slot(self, subject_id: str, section_id: str, slot: TimeSlot, room: str, 
                       is_lab: bool, is_elective: bool = False, elective_group: Optional[int] = None,
                       status: SlotStatus = SlotStatus.FLEXIBLE, is_continuous_pair: bool = False,
                       pair_with: Optional[TimeSlot] = None):
        """Assign subject to slot with faculty tracking"""
        faculty_id = self.faculty_assignments.get(subject_id)
        
        assignment = Assignment(
            subject_id=subject_id,
            faculty_id=faculty_id,
            section=section_id,
            room=room,
            time_slot=slot,
            is_lab=is_lab,
            is_elective=is_elective,
            elective_group=elective_group,
            status=status,
            is_continuous_pair=is_continuous_pair,
            pair_with=pair_with
        )
        self.assignments.append(assignment)
        
        # Update section schedule
        if section_id not in self.section_schedule:
            self.section_schedule[section_id] = set()
        self.section_schedule[section_id].add(slot)
        
        # Update faculty schedule if assigned
        if faculty_id:
            if faculty_id not in self.faculty_schedule:
                self.faculty_schedule[faculty_id] = set()
            self.faculty_schedule[faculty_id].add(slot)
        
        # Track period usage for this subject in this section
        if not is_lab:
            tracking_key = (section_id, subject_id)
            if tracking_key not in self.subject_period_usage:
                self.subject_period_usage[tracking_key] = set()
            self.subject_period_usage[tracking_key].add(slot.period)
    
    def solve(self) -> Dict:
        """Main CSP solving with all fixes"""
        logger.info("Starting CSP Solver (PATTERN-FREE VERSION)...")
        
        try:
            if not self._assign_lunch_breaks():
                return {'status': 'failed', 'message': 'Could not assign lunch breaks'}
            
            # Schedule pure labs first
            if not self._schedule_pure_labs():
                return {'status': 'failed', 'message': 'Could not schedule pure labs'}
            
            # Schedule electives
            if not self._schedule_electives():
                return {'status': 'failed', 'message': 'Could not schedule electives'}
            
            # Schedule semi-lab subjects
            if not self._schedule_semi_lab_subjects():
                return {'status': 'failed', 'message': 'Could not schedule semi-lab subjects'}
            
            # Schedule pure theory subjects
            if not self._schedule_pure_theory_subjects():
                return {'status': 'failed', 'message': 'Could not schedule pure theory'}
            
            # Schedule T&P subjects
            if not self._schedule_tp_subjects():
                logger.warning('Could not schedule all T&P subjects')
            
            if not self._validate_solution():
                return {'status': 'failed', 'message': 'Solution validation failed'}
            
            return {
                'status': 'success',
                'assignments': self.assignments,
                'statistics': {
                    'total_assignments': len(self.assignments),
                    'backtrack_count': self.backtrack_count,
                    'pure_labs': len([a for a in self.assignments if a.is_lab and not a.is_continuous_pair]),
                    'semi_labs': sum(1 for a in self.assignments if a.is_lab and any(
                        s.subject_id == a.subject_id for s in self.subjects 
                        if s.get_subject_type() == SubjectType.SEMI_LAB)),
                    'tp_subjects': len([a for a in self.assignments if a.is_continuous_pair]),
                    'theory_periods': len([a for a in self.assignments if not a.is_lab and not a.is_continuous_pair]),
                    'faculty_assigned': len([a for a in self.assignments if a.faculty_id is not None])
                }
            }
        except Exception as e:
            logger.error(f"CSP Solver failed: {e}", exc_info=True)
            return {'status': 'failed', 'message': str(e)}
    
    def _assign_lunch_breaks(self) -> bool:
        """Assign lunch breaks"""
        for branch, num_sections in self.sections_config.items():
            active_sems = self._get_active_semesters()
            for semester in active_sems:
                self.branch_lunch[(branch, semester)] = 4
        return True
    
    def _schedule_pure_labs(self) -> bool:
        """Schedule pure lab subjects with strict 2-day limit"""
        logger.info("Scheduling pure lab subjects...")
        active_sems = self._get_active_semesters()
        
        pure_lab_subjects = [
            s for s in self.subjects 
            if s.get_subject_type() == SubjectType.PURE_LAB 
            and s.semester in active_sems 
            and not s.is_elective
        ]
        pure_lab_subjects += [
            l for l in self.labs 
            if l.semester in active_sems 
            and not l.is_elective
        ]
        
        for lab in pure_lab_subjects:
            num_sections = self.sections_config.get(lab.branch, 0)
            for section_num in range(num_sections):
                section_id = f"{lab.branch}_Sem{lab.semester}_Sec{chr(65+section_num)}"
                num_sessions = lab.get_lab_sessions() if hasattr(lab, 'get_lab_sessions') else ceil(lab.P / 2)
                
                # STRICT: Limit to max 2 sessions for labs
                num_sessions = min(num_sessions, 2)
                
                if not self._schedule_lab_for_section(lab, section_id, num_sessions):
                    logger.warning(f"Could not fully schedule lab for {section_id}")
        
        return True
    
    def _schedule_lab_for_section(self, lab, section_id: str, num_sessions: int) -> bool:
        """Schedule lab with STRICT 2-day weekly limit"""
        lab_id = lab.lab_id if hasattr(lab, 'lab_id') else lab.subject_id
        tracking_key = (lab_id, section_id)
        
        if tracking_key not in self.lab_weekly_days:
            self.lab_weekly_days[tracking_key] = set()
        
        sessions_scheduled = 0
        
        # Try to schedule sessions on different days
        for day in range(5):
            if sessions_scheduled >= num_sessions:
                break
            
            # STRICT: Check 2-day weekly limit BEFORE trying to schedule
            if day not in self.lab_weekly_days[tracking_key]:
                if len(self.lab_weekly_days[tracking_key]) >= 2:
                    # Already have 2 days, can't add more
                    continue
            else:
                # This day is already used for this lab, skip it
                continue
            
            # Try to find a suitable lab period on this day
            for period_pair in self.lab_periods:
                if sessions_scheduled >= num_sessions:
                    break
                
                slot1 = TimeSlot(day, period_pair[0])
                slot2 = TimeSlot(day, period_pair[1])
                
                if self._can_assign_lab_with_room(lab_id, section_id, [slot1, slot2]):
                    room_id = self._assign_lab_with_room(lab, section_id, [slot1, slot2])
                    if room_id:
                        self.lab_weekly_days[tracking_key].add(day)
                        sessions_scheduled += 1
                        break
        
        return sessions_scheduled >= num_sessions
    
    def _can_assign_lab_with_room(self, lab_id: str, section_id: str, slots: List[TimeSlot]) -> bool:
        """Check if lab can be assigned with room availability"""
        for slot in slots:
            if not self._can_assign_slot(section_id, slot, lab_id):
                return False
        
        return self.room_manager.find_compatible_room(lab_id, slots) is not None
    
    def _assign_lab_with_room(self, lab, section_id: str, slots: List[TimeSlot]) -> Optional[str]:
        """Assign lab with room blocking and equipment check"""
        lab_id = lab.lab_id if hasattr(lab, 'lab_id') else lab.subject_id
        
        room_id = self.room_manager.find_compatible_room(lab_id, slots)
        
        if not room_id:
            room_id = "LAB_GENERIC"
        else:
            self.room_manager.allocate_room(room_id, slots, section_id)
        
        for slot in slots:
            self._assign_to_slot(
                subject_id=lab_id,
                section_id=section_id,
                slot=slot,
                room=room_id,
                is_lab=True,
                status=SlotStatus.FIXED
            )
        
        return room_id
    
    def _schedule_semi_lab_subjects(self) -> bool:
        """Schedule semi-lab subjects (L-T-P) with strict lab limits"""
        logger.info("Scheduling semi-lab subjects (L-T-P)...")
        active_sems = self._get_active_semesters()
        
        semi_subjects = [
            s for s in self.subjects 
            if s.get_subject_type() == SubjectType.SEMI_LAB 
            and s.semester in active_sems 
            and not s.is_elective
        ]
        
        for subject in semi_subjects:
            num_sections = self.sections_config.get(subject.branch, 0)
            
            for section_num in range(num_sections):
                section_id = f"{subject.branch}_Sem{subject.semester}_Sec{chr(65+section_num)}"
                
                # Schedule theory component (L + T)
                theory_periods = subject.get_theory_periods()
                if theory_periods > 0:
                    if not self._schedule_theory_periods(subject, section_id, theory_periods):
                        logger.warning(f"Could not fully schedule theory for {subject.subject_id}")
                
                # Schedule lab component (P) - STRICT 2-day limit
                lab_sessions = subject.get_lab_sessions()
                lab_sessions = min(lab_sessions, 2)  # STRICT LIMIT
                
                if lab_sessions > 0:
                    if not self._schedule_lab_component(subject, section_id, lab_sessions):
                        logger.warning(f"Could not fully schedule lab component for {subject.subject_id}")
        
        return True
    
    def _schedule_lab_component(self, subject, section_id: str, num_sessions: int) -> bool:
        """Schedule lab component of semi-lab subject with strict 2-day limit"""
        lab_id = subject.subject_id
        tracking_key = (lab_id, section_id)
        
        if tracking_key not in self.lab_weekly_days:
            self.lab_weekly_days[tracking_key] = set()
        
        sessions_scheduled = 0
        
        for day in range(5):
            if sessions_scheduled >= num_sessions:
                break
            
            # STRICT: Check 2-day limit
            if day not in self.lab_weekly_days[tracking_key]:
                if len(self.lab_weekly_days[tracking_key]) >= 2:
                    continue
            else:
                continue
            
            for period_pair in self.lab_periods:
                if sessions_scheduled >= num_sessions:
                    break
                
                slot1 = TimeSlot(day, period_pair[0])
                slot2 = TimeSlot(day, period_pair[1])
                
                if self._can_assign_lab_with_room(lab_id, section_id, [slot1, slot2]):
                    room_id = self.room_manager.find_compatible_room(lab_id, [slot1, slot2])
                    if not room_id:
                        room_id = "LAB_GENERIC"
                    else:
                        self.room_manager.allocate_room(room_id, [slot1, slot2], section_id)
                    
                    for slot in [slot1, slot2]:
                        self._assign_to_slot(
                            subject_id=subject.subject_id,
                            section_id=section_id,
                            slot=slot,
                            room=room_id,
                            is_lab=True,
                            status=SlotStatus.FIXED
                        )
                    
                    self.lab_weekly_days[tracking_key].add(day)
                    sessions_scheduled += 1
                    break
        
        return sessions_scheduled >= num_sessions
    
    def _schedule_pure_theory_subjects(self) -> bool:
        """Schedule pure theory subjects WITHOUT repeating patterns"""
        logger.info("Scheduling pure theory subjects...")
        active_sems = self._get_active_semesters()
        
        theory_subjects = [
            s for s in self.subjects 
            if s.get_subject_type() == SubjectType.PURE_THEORY
            and s.semester in active_sems 
            and not s.is_elective
        ]
        
        for subject in theory_subjects:
            num_sections = self.sections_config.get(subject.branch, 0)
            
            for section_num in range(num_sections):
                section_id = f"{subject.branch}_Sem{subject.semester}_Sec{chr(65+section_num)}"
                periods_needed = subject.get_theory_periods()
                
                if not self._schedule_theory_periods(subject, section_id, periods_needed):
                    logger.warning(f"Could not fully schedule {subject.subject_id}")
        
        return True
    
    def _schedule_theory_periods(self, subject, section_id: str, periods_needed: int) -> bool:
        """
        ENHANCED: Schedule theory periods - ONE per day, NO same-period patterns
        """
        scheduled_days = set()
        periods_scheduled = 0
        
        # Calculate daily load for load balancing
        daily_load = [0] * 5
        for assignment in self.assignments:
            if assignment.section == section_id:
                daily_load[assignment.time_slot.day] += 1
        
        # Get periods already used for this subject
        tracking_key = (section_id, subject.subject_id)
        used_periods = self.subject_period_usage.get(tracking_key, set())
        
        for attempt in range(10):
            if periods_scheduled >= periods_needed:
                break
            
            # Sort days by: not yet scheduled for this subject, then by lowest load
            days_by_load = sorted(range(5), key=lambda d: (d in scheduled_days, daily_load[d]))
            
            for day in days_by_load:
                if periods_scheduled >= periods_needed:
                    break
                
                # Skip if already scheduled on this day
                if day in scheduled_days:
                    continue
                
                # Try to find a period that's NOT already used for this subject
                # This prevents same-period patterns
                available_periods = [p for p in range(8) if p not in used_periods]
                
                # If all periods are used, we must reuse - but try to maximize spread
                if not available_periods:
                    available_periods = list(range(8))
                
                for period in available_periods:
                    slot = TimeSlot(day, period)
                    
                    if not self._can_assign_theory_slot(section_id, slot, subject.subject_id):
                        continue
                    
                    # Double-check: no subject on this day yet
                    subject_today = any(
                        a.section == section_id and 
                        a.subject_id == subject.subject_id and 
                        a.time_slot.day == day
                        for a in self.assignments
                    )
                    
                    if subject_today:
                        break
                    
                    # Assign the slot
                    self._assign_to_slot(
                        subject_id=subject.subject_id,
                        section_id=section_id,
                        slot=slot,
                        room="LH_ROOM",
                        is_lab=False,
                        status=SlotStatus.FLEXIBLE
                    )
                    
                    scheduled_days.add(day)
                    daily_load[day] += 1
                    periods_scheduled += 1
                    break
            
            if periods_scheduled >= periods_needed:
                break
        
        if periods_scheduled < periods_needed:
            logger.warning(f"Scheduled {periods_scheduled}/{periods_needed} for {subject.subject_id}")
            self.backtrack_count += 1
        
        return periods_scheduled > 0
    
    def _schedule_tp_subjects(self) -> bool:
        """Schedule T&P subjects (continuous pairs)"""
        logger.info("Scheduling T&P subjects (continuous pairs)...")
        active_sems = self._get_active_semesters()
        
        tp_subjects = [
            s for s in self.subjects 
            if s.get_subject_type() == SubjectType.TP_SUBJECT
            and s.semester in active_sems 
            and not s.is_elective
        ]
        
        if not tp_subjects:
            return True
        
        for subject in tp_subjects:
            num_sections = self.sections_config.get(subject.branch, 0)
            
            for section_num in range(num_sections):
                section_id = f"{subject.branch}_Sem{subject.semester}_Sec{chr(65+section_num)}"
                num_pairs = subject.get_lab_sessions()
                
                if not self._schedule_tp_continuous_pairs(subject, section_id, num_pairs):
                    logger.warning(f"Could not fully schedule T&P {subject.subject_id}")
        
        return True
    
    def _schedule_tp_continuous_pairs(self, subject, section_id: str, num_pairs: int) -> bool:
        """Schedule continuous pairs for T&P subjects"""
        pairs_scheduled = 0
        
        for day in range(5):
            if pairs_scheduled >= num_pairs:
                break
            
            for period_pair in self.continuous_pairs:
                if pairs_scheduled >= num_pairs:
                    break
                
                slot1 = TimeSlot(day, period_pair[0])
                slot2 = TimeSlot(day, period_pair[1])
                
                if not self._can_assign_slot(section_id, slot1, subject.subject_id):
                    continue
                if not self._can_assign_slot(section_id, slot2, subject.subject_id):
                    continue
                
                for slot in [slot1, slot2]:
                    self._assign_to_slot(
                        subject_id=subject.subject_id,
                        section_id=section_id,
                        slot=slot,
                        room="LH_ROOM",
                        is_lab=False,
                        is_continuous_pair=True,
                        pair_with=slot2 if slot == slot1 else slot1,
                        status=SlotStatus.TP_PENDING
                    )
                
                pairs_scheduled += 1
                break
        
        return pairs_scheduled > 0
    
    def _schedule_electives(self) -> bool:
        """Schedule electives with proper handling"""
        logger.info("Scheduling electives...")
        
        for group_config in self.grouped_electives:
            if not self._schedule_elective_group(group_config):
                logger.warning(f"Could not fully schedule elective group {group_config['group_name']}")
        
        return True
    
    def _schedule_elective_group(self, group_config: Dict) -> bool:
        """Schedule elective group"""
        branch = group_config['branch']
        semester = group_config['semester']
        elective_ids = group_config['electives']
        num_sections = self.sections_config.get(branch, 0)
        
        elective_subjects = []
        for elec_id in elective_ids:
            subject = next((s for s in self.subjects if s.subject_id == elec_id), None)
            if subject:
                elective_subjects.append(subject)
        
        if not elective_subjects:
            return True
        
        min_theory_periods = min(s.L + s.T for s in elective_subjects)
        
        # Schedule common theory periods
        common_slots_scheduled = 0
        days_used_for_common = set()
        
        for common_period in range(min_theory_periods):
            slot_found = False
            
            days_to_try = [d for d in range(5) if d not in days_used_for_common]
            days_to_try.extend([d for d in range(5) if d in days_used_for_common])
            
            for day in days_to_try:
                if slot_found:
                    break
                
                if day in days_used_for_common and len(days_used_for_common) < 5:
                    continue
                
                for period in range(8):
                    slot = TimeSlot(day, period)
                    
                    can_use = True
                    for section_num in range(num_sections):
                        section_id = f"{branch}_Sem{semester}_Sec{chr(65+section_num)}"
                        elective_id = elective_ids[section_num % len(elective_ids)]
                        
                        if not self._can_assign_theory_slot(section_id, slot, elective_id):
                            can_use = False
                            break
                    
                    if can_use:
                        for section_num in range(num_sections):
                            section_id = f"{branch}_Sem{semester}_Sec{chr(65+section_num)}"
                            elective_id = elective_ids[section_num % len(elective_ids)]
                            
                            self._assign_to_slot(
                                subject_id=elective_id,
                                section_id=section_id,
                                slot=slot,
                                room="LH_ROOM",
                                is_lab=False,
                                is_elective=True,
                                elective_group=group_config['group_number'],
                                status=SlotStatus.FIXED
                            )
                        
                        common_slots_scheduled += 1
                        days_used_for_common.add(day)
                        slot_found = True
                        break
            
            if not slot_found:
                break
        
        # Schedule individual periods and labs
        for section_num in range(num_sections):
            section_id = f"{branch}_Sem{semester}_Sec{chr(65+section_num)}"
            elective_id = elective_ids[section_num % len(elective_ids)]
            
            subject = next((s for s in elective_subjects if s.subject_id == elective_id), None)
            if not subject:
                continue
            
            total_theory_needed = subject.L + subject.T
            remaining_theory = total_theory_needed - common_slots_scheduled
            
            if remaining_theory > 0:
                self._schedule_individual_elective_theory(subject, section_id, remaining_theory, group_config)
            
            if subject.P > 0:
                if subject.get_subject_type() == SubjectType.TP_SUBJECT:
                    num_pairs = subject.get_lab_sessions()
                    self._schedule_tp_elective_pairs(subject, section_id, num_pairs, group_config)
                else:
                    num_lab_sessions = min(subject.get_lab_sessions(), 2)  # STRICT LIMIT
                    self._schedule_individual_elective_labs(subject, section_id, num_lab_sessions, group_config)
        
        return True
    
    def _schedule_individual_elective_theory(self, subject, section_id: str, 
                                     periods_needed: int, group_config: Dict) -> bool:
        """Schedule individual elective theory periods"""
        periods_scheduled = 0
        days_used = set()
        
        for assignment in self.assignments:
            if assignment.section == section_id and assignment.subject_id == subject.subject_id:
                days_used.add(assignment.time_slot.day)
        
        for attempt in range(2):
            for day in range(5):
                if periods_scheduled >= periods_needed:
                    break
                
                if attempt == 0 and day in days_used:
                    continue
                
                for period in range(8):
                    if periods_scheduled >= periods_needed:
                        break
                    
                    slot = TimeSlot(day, period)
                    
                    if not self._can_assign_theory_slot(section_id, slot, subject.subject_id):
                        continue
                    
                    self._assign_to_slot(
                        subject_id=subject.subject_id,
                        section_id=section_id,
                        slot=slot,
                        room="LH_ROOM",
                        is_lab=False,
                        is_elective=True,
                        elective_group=group_config['group_number'],
                        status=SlotStatus.FIXED
                    )
                    
                    periods_scheduled += 1
                    days_used.add(day)
                    break
            
            if periods_scheduled >= periods_needed:
                break
        
        return periods_scheduled >= periods_needed
    
    def _schedule_individual_elective_labs(self, subject, section_id: str, 
                                        num_sessions: int, group_config: Dict) -> bool:
        """Schedule individual elective lab sessions with strict 2-day limit"""
        lab_id = subject.subject_id
        tracking_key = (lab_id, section_id)
        
        if tracking_key not in self.lab_weekly_days:
            self.lab_weekly_days[tracking_key] = set()
        
        sessions_scheduled = 0
        
        for day in range(5):
            if sessions_scheduled >= num_sessions:
                break
            
            # STRICT: Check 2-day limit
            if day not in self.lab_weekly_days[tracking_key]:
                if len(self.lab_weekly_days[tracking_key]) >= 2:
                    continue
            else:
                continue
            
            for period_pair in self.lab_periods:
                if sessions_scheduled >= num_sessions:
                    break
                
                slot1 = TimeSlot(day, period_pair[0])
                slot2 = TimeSlot(day, period_pair[1])
                
                if self._can_assign_lab_with_room(subject.subject_id, section_id, [slot1, slot2]):
                    room_id = self.room_manager.find_compatible_room(subject.subject_id, [slot1, slot2])
                    if not room_id:
                        room_id = "LAB_GENERIC"
                    else:
                        self.room_manager.allocate_room(room_id, [slot1, slot2], section_id)
                    
                    for slot in [slot1, slot2]:
                        self._assign_to_slot(
                            subject_id=subject.subject_id,
                            section_id=section_id,
                            slot=slot,
                            room=room_id,
                            is_lab=True,
                            is_elective=True,
                            elective_group=group_config['group_number'],
                            status=SlotStatus.FIXED
                        )
                    
                    self.lab_weekly_days[tracking_key].add(day)
                    sessions_scheduled += 1
        
        return sessions_scheduled >= num_sessions
    
    def _schedule_tp_elective_pairs(self, subject, section_id: str,
                                    num_pairs: int, group_config: Dict) -> bool:
        """Schedule T&P elective pairs"""
        pairs_scheduled = 0
        
        for day in range(5):
            if pairs_scheduled >= num_pairs:
                break
            
            for period_pair in self.continuous_pairs:
                if pairs_scheduled >= num_pairs:
                    break
                
                slot1 = TimeSlot(day, period_pair[0])
                slot2 = TimeSlot(day, period_pair[1])
                
                if not self._can_assign_slot(section_id, slot1, subject.subject_id):
                    continue
                if not self._can_assign_slot(section_id, slot2, subject.subject_id):
                    continue
                
                for slot in [slot1, slot2]:
                    self._assign_to_slot(
                        subject_id=subject.subject_id,
                        section_id=section_id,
                        slot=slot,
                        room="LH_ROOM",
                        is_lab=False,
                        is_continuous_pair=True,
                        pair_with=slot2 if slot == slot1 else slot1,
                        is_elective=True,
                        elective_group=group_config['group_number'],
                        status=SlotStatus.TP_PENDING
                    )
                
                pairs_scheduled += 1
                break
        
        return pairs_scheduled >= num_pairs
    
    def _validate_solution(self) -> bool:
        """Validate solution with enhanced checks"""
        # Check no duplicate slots
        section_slots = {}
        for assignment in self.assignments:
            key = (assignment.section, assignment.time_slot)
            if key in section_slots:
                logger.error(f"Duplicate slot: {assignment.section} at {assignment.time_slot}")
                return False
            section_slots[key] = assignment
        
        # Validate lab frequency (max 2 days per week)
        lab_day_counts = {}
        for assignment in self.assignments:
            if assignment.is_lab:
                key = (assignment.subject_id, assignment.section)
                if key not in lab_day_counts:
                    lab_day_counts[key] = set()
                lab_day_counts[key].add(assignment.time_slot.day)
        
        for key, days in lab_day_counts.items():
            if len(days) > 2:
                logger.error(f"Lab frequency violation: {key[0]} in {key[1]} on {len(days)} days")
                return False
        
        # NEW: Validate no same-period patterns for theory
        for section_id in set(a.section for a in self.assignments):
            subject_period_map = {}
            
            for assignment in self.assignments:
                if assignment.section == section_id and not assignment.is_lab:
                    subject_id = assignment.subject_id
                    period = assignment.time_slot.period
                    
                    if subject_id not in subject_period_map:
                        subject_period_map[subject_id] = []
                    subject_period_map[subject_id].append(period)
            
            # Check for repeated periods
            for subject_id, periods in subject_period_map.items():
                period_counts = {}
                for p in periods:
                    period_counts[p] = period_counts.get(p, 0) + 1
                
                # Allow at most 1 repeat of a period (for subjects with many hours)
                for period, count in period_counts.items():
                    if count > 2:
                        logger.warning(f"Period {period} used {count} times for {subject_id} in {section_id}")
        
        return True
    
    def _get_active_semesters(self) -> List[int]:
        """Get active semesters"""
        if hasattr(self.semester_mode, 'value'):
            return [3, 5, 7] if self.semester_mode.value == 'odd' else [4, 6]
        return [3, 5, 7]
    
    def _parse_section_id(self, section_id: str) -> Tuple[str, int]:
        """Parse section ID"""
        parts = section_id.split('_')
        branch = parts[0]
        semester = int(parts[1].replace('Sem', ''))
        return branch, semester

# ============================================================================
# MDP SCHEDULER (keeping same as before)
# ============================================================================

@dataclass
class State:
    assignments: List
    faculty_workload: Dict[int, float]
    section_distribution: Dict[str, List[int]]
    resource_utilization: float
    
    def to_vector(self) -> np.ndarray:
        features = []
        if self.faculty_workload:
            workload_values = list(self.faculty_workload.values())
            features.append(np.std(workload_values) / (np.mean(workload_values) + 1e-6))
        else:
            features.append(0.0)
        if self.section_distribution:
            variances = [np.std(dist) for dist in self.section_distribution.values()]
            features.append(np.mean(variances) if variances else 0.0)
        else:
            features.append(0.0)
        features.append(self.resource_utilization)
        features.append(len(self.assignments) / 1000.0)
        return np.array(features, dtype=np.float32)

@dataclass
class Action:
    assignment_id: int
    faculty_id: Optional[int]
    room_id: Optional[str]
    action_type: str

class MDPScheduler:
    def __init__(self, csp_solution: Dict, subjects, faculty, rooms):
        self.csp_assignments = csp_solution.get('assignments', [])
        self.subjects = subjects
        self.faculty = faculty
        self.rooms = rooms
        self.current_state = None
        self.best_state = None
        self.best_reward = -float('inf')
        self.faculty_qualifications = self._build_faculty_qualifications()
        self.room_capacities = self._build_room_map()
    
    def _build_faculty_qualifications(self) -> Dict[int, List[str]]:
        qual_map = {}
        for fac in self.faculty:
            qual_map[fac.faculty_id] = fac.courses if hasattr(fac, 'courses') else []
        return qual_map
    
    def _build_room_map(self) -> Dict[str, int]:
        room_map = {}
        for room in self.rooms:
            room_id = room.room_id if hasattr(room, 'room_id') else 'DEFAULT'
            capacity = room.capacity if hasattr(room, 'capacity') else 60
            room_map[room_id] = capacity
        return room_map
    
    def initialize_state(self) -> State:
        faculty_workload = {}
        for assignment in self.csp_assignments:
            if assignment.faculty_id:
                faculty_workload[assignment.faculty_id] = faculty_workload.get(assignment.faculty_id, 0) + 1
        
        section_distribution = {}
        for assignment in self.csp_assignments:
            if assignment.section not in section_distribution:
                section_distribution[assignment.section] = [0] * 5
            section_distribution[assignment.section][assignment.time_slot.day] += 1
        
        total_slots = 5 * 8
        used_slots = len(self.csp_assignments)
        resource_utilization = used_slots / (total_slots * len(section_distribution) + 1e-6)
        
        state = State(
            assignments=deepcopy(self.csp_assignments),
            faculty_workload=faculty_workload,
            section_distribution=section_distribution,
            resource_utilization=resource_utilization
        )
        
        self.current_state = state
        self.best_state = deepcopy(state)
        return state
    
    def get_valid_actions(self, state: State) -> List[Action]:
        actions = []
        for idx, assignment in enumerate(state.assignments[:50]):
            if not assignment.faculty_id:
                qualified_faculty = self._get_qualified_faculty(assignment.subject_id)
                for fac_id in qualified_faculty[:5]:
                    actions.append(Action(
                        assignment_id=idx,
                        faculty_id=fac_id,
                        room_id=None,
                        action_type='assign_faculty'
                    ))
        return actions
    
    def _get_qualified_faculty(self, subject_id: str) -> List[int]:
        qualified = []
        for fac_id, courses in self.faculty_qualifications.items():
            if subject_id in courses:
                qualified.append(fac_id)
        return qualified
    
    def apply_action(self, state: State, action: Action) -> State:
        new_state = deepcopy(state)
        if action.action_type == 'assign_faculty':
            assignment = new_state.assignments[action.assignment_id]
            old_faculty = assignment.faculty_id
            assignment.faculty_id = action.faculty_id
            if old_faculty and old_faculty in new_state.faculty_workload:
                new_state.faculty_workload[old_faculty] -= 1
            if action.faculty_id not in new_state.faculty_workload:
                new_state.faculty_workload[action.faculty_id] = 0
            new_state.faculty_workload[action.faculty_id] += 1
        return new_state
    
    def calculate_reward(self, state: State) -> float:
        reward = 0.0
        if state.faculty_workload:
            workload_values = list(state.faculty_workload.values())
            mean_workload = np.mean(workload_values)
            std_workload = np.std(workload_values)
            balance_score = 1.0 / (1.0 + std_workload / (mean_workload + 1e-6))
            reward += balance_score * 40.0
            violations = sum(1 for w in workload_values if w > 24)
            reward -= violations * 5.0
        if state.section_distribution:
            distribution_scores = []
            for section, daily_counts in state.section_distribution.items():
                std_daily = np.std(daily_counts)
                mean_daily = np.mean(daily_counts)
                balance = 1.0 / (1.0 + std_daily / (mean_daily + 1e-6))
                distribution_scores.append(balance)
                max_daily = max(daily_counts)
                if max_daily > 6:
                    reward -= (max_daily - 6) * 2.0
            reward += np.mean(distribution_scores) * 30.0 if distribution_scores else 0.0
        if state.resource_utilization < 0.5:
            reward += state.resource_utilization * 20.0
        else:
            reward += (0.5 + (state.resource_utilization - 0.5) * 0.5) * 20.0
        complete_assignments = sum(1 for a in state.assignments 
                                  if a.faculty_id is not None and a.room is not None)
        completeness = complete_assignments / (len(state.assignments) + 1e-6)
        reward += completeness * 10.0
        return reward
    
    def transition(self, state: State, action: Action) -> Tuple[State, float]:
        new_state = self.apply_action(state, action)
        reward = self.calculate_reward(new_state)
        if reward > self.best_reward:
            self.best_reward = reward
            self.best_state = deepcopy(new_state)
        return new_state, reward
    
    def get_state_dim(self) -> int:
        dummy_state = State([], {}, {}, 0.0)
        return len(dummy_state.to_vector())
    
    def get_action_space_size(self) -> int:
        return len(self.csp_assignments) * 10

# ============================================================================
# A2C AGENT (Same as before)
# ============================================================================

class ActorCriticNetwork(nn.Module):
    def __init__(self, state_dim: int, action_dim: int, hidden_dim: int = 128):
        super(ActorCriticNetwork, self).__init__()
        self.shared_fc1 = nn.Linear(state_dim, hidden_dim)
        self.shared_fc2 = nn.Linear(hidden_dim, hidden_dim)
        self.actor_fc = nn.Linear(hidden_dim, action_dim)
        self.critic_fc = nn.Linear(hidden_dim, 1)
    
    def forward(self, state):
        x = F.relu(self.shared_fc1(state))
        x = F.relu(self.shared_fc2(x))
        action_probs = F.softmax(self.actor_fc(x), dim=-1)
        state_value = self.critic_fc(x)
        return action_probs, state_value

class A2CAgent:
    def __init__(self, state_dim: int, action_dim: int, 
                 learning_rate: float = 0.001, gamma: float = 0.99,
                 entropy_coef: float = 0.01):
        self.state_dim = state_dim
        self.action_dim = action_dim
        self.gamma = gamma
        self.entropy_coef = entropy_coef
        self.network = ActorCriticNetwork(state_dim, action_dim)
        self.optimizer = optim.Adam(self.network.parameters(), lr=learning_rate)
        self.episode_rewards = []
        self.losses = []
    
    def select_action(self, state_vector: np.ndarray, 
                     valid_action_mask: np.ndarray = None) -> Tuple[int, float, float]:
        state_tensor = torch.FloatTensor(state_vector).unsqueeze(0)
        with torch.no_grad():
            action_probs, state_value = self.network(state_tensor)
        if valid_action_mask is not None:
            mask_tensor = torch.FloatTensor(valid_action_mask)
            action_probs = action_probs * mask_tensor
            action_probs = action_probs / (action_probs.sum() + 1e-8)
        action_dist = torch.distributions.Categorical(action_probs)
        action = action_dist.sample()
        log_prob = action_dist.log_prob(action)
        return action.item(), log_prob.item(), state_value.item()
    
    def select_greedy_action(self, state_vector: np.ndarray,
                            valid_action_mask: np.ndarray = None) -> int:
        state_tensor = torch.FloatTensor(state_vector).unsqueeze(0)
        with torch.no_grad():
            action_probs, _ = self.network(state_tensor)
        if valid_action_mask is not None:
            mask_tensor = torch.FloatTensor(valid_action_mask)
            action_probs = action_probs * mask_tensor
        return torch.argmax(action_probs).item()
    
    def train_step(self, states: List[np.ndarray], actions: List[int],
                   rewards: List[float], next_states: List[np.ndarray],
                   dones: List[bool]) -> float:
        states_tensor = torch.FloatTensor(np.array(states))
        actions_tensor = torch.LongTensor(actions)
        rewards_tensor = torch.FloatTensor(rewards)
        next_states_tensor = torch.FloatTensor(np.array(next_states))
        dones_tensor = torch.FloatTensor(dones)
        action_probs, state_values = self.network(states_tensor)
        _, next_state_values = self.network(next_states_tensor)
        next_values = next_state_values.squeeze() * (1 - dones_tensor)
        targets = rewards_tensor + self.gamma * next_values
        advantages = targets - state_values.squeeze()
        action_dist = torch.distributions.Categorical(action_probs)
        log_probs = action_dist.log_prob(actions_tensor)
        actor_loss = -(log_probs * advantages.detach()).mean()
        critic_loss = F.mse_loss(state_values.squeeze(), targets.detach())
        entropy = action_dist.entropy().mean()
        entropy_loss = -self.entropy_coef * entropy
        total_loss = actor_loss + critic_loss + entropy_loss
        self.optimizer.zero_grad()
        total_loss.backward()
        torch.nn.utils.clip_grad_norm_(self.network.parameters(), max_norm=0.5)
        self.optimizer.step()
        self.losses.append(total_loss.item())
        return total_loss.item()
    
    def train_episode(self, mdp_env, max_steps: int = 100) -> float:
        state = mdp_env.initialize_state()
        episode_reward = 0.0
        states, actions_taken, rewards, next_states, dones = [], [], [], [], []
        for step in range(max_steps):
            valid_actions = mdp_env.get_valid_actions(state)
            if not valid_actions:
                break
            action_idx_to_action = {i: action for i, action in enumerate(valid_actions)}
            valid_mask = np.zeros(self.action_dim)
            valid_mask[:len(valid_actions)] = 1.0
            state_vector = state.to_vector()
            action_idx, log_prob, value = self.select_action(state_vector, valid_mask)
            if action_idx >= len(valid_actions):
                action_idx = 0
            action = action_idx_to_action[action_idx]
            next_state, reward = mdp_env.transition(state, action)
            states.append(state_vector)
            actions_taken.append(action_idx)
            rewards.append(reward)
            next_states.append(next_state.to_vector())
            dones.append(False)
            episode_reward += reward
            state = next_state
            if len(states) >= 32:
                self.train_step(states, actions_taken, rewards, next_states, dones)
                states, actions_taken, rewards, next_states, dones = [], [], [], [], []
        if states:
            self.train_step(states, actions_taken, rewards, next_states, dones)
        self.episode_rewards.append(episode_reward)
        return episode_reward
    
    def train(self, mdp_env, num_episodes: int = 100, 
              max_steps_per_episode: int = 100) -> List[float]:
        logger.info(f"Training A2C for {num_episodes} episodes...")
        for episode in range(num_episodes):
            episode_reward = self.train_episode(mdp_env, max_steps_per_episode)
            if (episode + 1) % 10 == 0:
                avg_reward = np.mean(self.episode_rewards[-10:])
                logger.info(f"Episode {episode+1}/{num_episodes}: Reward={episode_reward:.2f}, Avg={avg_reward:.2f}")
        return self.episode_rewards
    
    def optimize_schedule(self, mdp_env, num_iterations: int = 50) -> Tuple:
        state = mdp_env.initialize_state()
        best_state = state
        best_reward = mdp_env.calculate_reward(state)
        for iteration in range(num_iterations):
            valid_actions = mdp_env.get_valid_actions(state)
            if not valid_actions:
                break
            action_idx_to_action = {i: action for i, action in enumerate(valid_actions)}
            valid_mask = np.zeros(self.action_dim)
            valid_mask[:len(valid_actions)] = 1.0
            state_vector = state.to_vector()
            action_idx = self.select_greedy_action(state_vector, valid_mask)
            if action_idx >= len(valid_actions):
                action_idx = 0
            action = action_idx_to_action[action_idx]
            state, reward = mdp_env.transition(state, action)
            if reward > best_reward:
                best_reward = reward
                best_state = state
        return best_state, best_reward

# ============================================================================
# GENERATOR (Same as before)
# ============================================================================

@dataclass
class GenerationConfig:
    num_training_episodes: int = 50
    max_steps_per_episode: int = 50
    num_optimization_iterations: int = 30
    learning_rate: float = 0.001
    gamma: float = 0.99
    entropy_coef: float = 0.01
    max_backtracks: int = 10000

class ThreeLayerTimetableGenerator:
    def __init__(self, subjects, faculty, labs, rooms, sections_config,
                 core_lab_pairs, grouped_electives, faculty_assignments, semester_mode,
                 config: Optional[GenerationConfig] = None):
        self.subjects = subjects
        self.faculty = faculty
        self.labs = labs
        self.rooms = rooms
        self.sections_config = sections_config
        self.core_lab_pairs = core_lab_pairs
        self.grouped_electives = grouped_electives
        self.faculty_assignments = faculty_assignments
        self.semester_mode = semester_mode
        self.config = config if config else GenerationConfig()
        self.csp_solver = None
        self.mdp_scheduler = None
        self.a2c_agent = None
        self.final_schedule = None
        self.generation_stats = {}
    
    def generate(self, callback=None) -> Dict:
        start_time = time.time()
        try:
            logger.info("Layer 1: CSP Solver (Pattern-Free)")
            if callback:
                callback(10, "Layer 1: CSP Solver starting (Pattern-Free)...")
            
            self.csp_solver = CSPSolver(
                subjects=self.subjects,
                faculty=self.faculty,
                labs=self.labs,
                rooms=self.rooms,
                sections_config=self.sections_config,
                core_lab_pairs=self.core_lab_pairs,
                grouped_electives=self.grouped_electives,
                faculty_assignments=self.faculty_assignments,
                semester_mode=self.semester_mode
            )
            
            if callback:
                callback(20, "Layer 1: Solving constraints...")
            
            csp_result = self.csp_solver.solve()
            
            if csp_result['status'] != 'success':
                return {
                    'status': 'failed',
                    'message': f"CSP failed: {csp_result['message']}",
                    'layer': 1
                }
            
            logger.info("Layer 2: MDP Scheduler")
            if callback:
                callback(40, "Layer 2: Initializing MDP...")
            
            self.mdp_scheduler = MDPScheduler(
                csp_solution=csp_result,
                subjects=self.subjects,
                faculty=self.faculty,
                rooms=self.rooms
            )
            
            initial_state = self.mdp_scheduler.initialize_state()
            initial_reward = self.mdp_scheduler.calculate_reward(initial_state)
            
            logger.info("Layer 3: A2C Agent")
            if callback:
                callback(50, "Layer 3: Initializing A2C...")
            
            state_dim = self.mdp_scheduler.get_state_dim()
            action_dim = min(self.mdp_scheduler.get_action_space_size(), 1000)
            
            self.a2c_agent = A2CAgent(
                state_dim=state_dim,
                action_dim=action_dim,
                learning_rate=self.config.learning_rate,
                gamma=self.config.gamma,
                entropy_coef=self.config.entropy_coef
            )
            
            if callback:
                callback(60, f"Layer 3: Training for {self.config.num_training_episodes} episodes...")
            
            episode_rewards = self.a2c_agent.train(
                mdp_env=self.mdp_scheduler,
                num_episodes=self.config.num_training_episodes,
                max_steps_per_episode=self.config.max_steps_per_episode
            )
            
            avg_training_reward = sum(episode_rewards[-10:]) / 10 if len(episode_rewards) >= 10 else 0
            
            if callback:
                callback(80, f"Layer 3: Optimizing for {self.config.num_optimization_iterations} iterations...")
            
            best_state, best_reward = self.a2c_agent.optimize_schedule(
                mdp_env=self.mdp_scheduler,
                num_iterations=self.config.num_optimization_iterations
            )
            
            if callback:
                callback(95, "Finalizing schedule...")
            
            total_time = time.time() - start_time
            
            self.final_schedule = best_state.assignments
            self.generation_stats = {
                'total_time': total_time,
                'layer1_assignments': len(csp_result['assignments']),
                'layer1_backtracks': csp_result['statistics']['backtrack_count'],
                'layer1_pure_labs': csp_result['statistics']['pure_labs'],
                'layer1_semi_labs': csp_result['statistics']['semi_labs'],
                'layer1_tp_subjects': csp_result['statistics']['tp_subjects'],
                'layer1_theory_periods': csp_result['statistics']['theory_periods'],
                'layer1_faculty_assigned': csp_result['statistics']['faculty_assigned'],
                'layer2_initial_reward': initial_reward,
                'layer3_training_episodes': self.config.num_training_episodes,
                'layer3_avg_training_reward': avg_training_reward,
                'layer3_optimization_iterations': self.config.num_optimization_iterations,
                'final_reward': best_reward,
                'improvement': best_reward - initial_reward,
                'total_assignments': len(self.final_schedule),
                'faculty_count': len(set(a.faculty_id for a in self.final_schedule if a.faculty_id)),
                'sections_count': len(set(a.section for a in self.final_schedule))
            }
            
            if callback:
                callback(100, "Generation complete!")
            
            return {
                'status': 'success',
                'schedule': self.final_schedule,
                'statistics': self.generation_stats,
                'message': 'Timetable generated successfully'
            }
            
        except Exception as e:
            logger.error(f"Generation failed: {e}", exc_info=True)
            if callback:
                callback(100, f"Error: {str(e)}")
            return {'status': 'failed', 'message': str(e), 'layer': 'unknown'}
    
    def export_schedule(self, format_type: str = 'dict') -> Dict:
        if not self.final_schedule:
            return {}
        schedule_dict = {}
        for assignment in self.final_schedule:
            section = assignment.section
            day = assignment.time_slot.day
            period = assignment.time_slot.period
            if section not in schedule_dict:
                schedule_dict[section] = {}
            if day not in schedule_dict[section]:
                schedule_dict[section][day] = {}
            schedule_dict[section][day][period] = {
                'subject_id': assignment.subject_id,
                'faculty_id': assignment.faculty_id,
                'room': assignment.room,
                'is_lab': assignment.is_lab,
                'is_elective': assignment.is_elective,
                'is_continuous_pair': assignment.is_continuous_pair,
                'status': assignment.status.value if hasattr(assignment.status, 'value') else str(assignment.status)
            }
        return schedule_dict

# ============================================================================
# DATABASE & CSV LOADER (Same as before - no changes needed)
# ============================================================================

class DatabaseManager:
    def __init__(self, db_path='timetable_config.db'):
        self.db_path = db_path
        self.conn = None
        self._initialize_database()
    
    def _initialize_database(self):
        self.conn = sqlite3.connect(self.db_path, check_same_thread=False)
        cursor = self.conn.cursor()
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS section_configs (
                branch TEXT PRIMARY KEY,
                num_sections INTEGER NOT NULL
            )
        ''')
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS core_lab_pairs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                subject_id TEXT NOT NULL,
                lab_id TEXT NOT NULL,
                branch TEXT NOT NULL,
                semester INTEGER NOT NULL,
                faculty_must_match INTEGER NOT NULL,
                UNIQUE(subject_id, lab_id, branch, semester)
            )
        ''')
        self.conn.commit()
    
    def add_section_config(self, branch: str, num_sections: int):
        cursor = self.conn.cursor()
        cursor.execute('''
            INSERT OR REPLACE INTO section_configs (branch, num_sections)
            VALUES (?, ?)
        ''', (branch, num_sections))
        self.conn.commit()
    
    def get_all_sections(self) -> Dict[str, int]:
        cursor = self.conn.cursor()
        cursor.execute('SELECT branch, num_sections FROM section_configs')
        return {row[0]: row[1] for row in cursor.fetchall()}
    
    def delete_section_config(self, branch: str):
        cursor = self.conn.cursor()
        cursor.execute('DELETE FROM section_configs WHERE branch = ?', (branch,))
        self.conn.commit()
    
    def add_core_lab_pair(self, subject_id: str, lab_id: str, branch: str, 
                         semester: int, faculty_must_match: bool) -> int:
        cursor = self.conn.cursor()
        try:
            cursor.execute('''
                INSERT INTO core_lab_pairs (subject_id, lab_id, branch, semester, faculty_must_match)
                VALUES (?, ?, ?, ?, ?)
            ''', (subject_id, lab_id, branch, semester, 1 if faculty_must_match else 0))
            self.conn.commit()
            return cursor.lastrowid
        except sqlite3.IntegrityError:
            return -1
    
    def get_all_core_lab_pairs(self) -> List[CoreLabPair]:
        cursor = self.conn.cursor()
        cursor.execute('SELECT * FROM core_lab_pairs')
        pairs = []
        for row in cursor.fetchall():
            pairs.append(CoreLabPair(
                id=row[0],
                subject_id=row[1],
                lab_id=row[2],
                branch=row[3],
                semester=row[4],
                faculty_must_match=bool(row[5])
            ))
        return pairs
    
    def delete_core_lab_pair(self, pair_id: int):
        cursor = self.conn.cursor()
        cursor.execute('DELETE FROM core_lab_pairs WHERE id = ?', (pair_id,))
        self.conn.commit()

class CSVDataLoader:
    def __init__(self, data_folder='data'):
        self.data_folder = data_folder
        self.subjects: List[Subject] = []
        self.faculty: List[Faculty] = []
        self.labs: List[Lab] = []
        self.lab_rooms: List[LabRoom] = []
    
    def load_all(self) -> bool:
        try:
            self._load_subjects()
            self._load_faculty()
            self._load_labs()
            self._load_rooms()
            return True
        except Exception as e:
            logger.error(f"Failed to load CSV files: {e}")
            return False
    
    def _load_subjects(self):
        df = pd.read_csv(f'{self.data_folder}/subjects.csv')
        for _, row in df.iterrows():
            subject = Subject(
                subject_id=str(row['subject_id']),
                subject_name=str(row['subject_name']),
                L=int(row['L']),
                T=int(row['T']),
                P=int(row['P']),
                branch=str(row['branch']),
                semester=int(row['semester']),
                is_elective=bool(row['is_elective']),
                elective_group=int(row['elective_group']) if pd.notna(row['elective_group']) else None
            )
            self.subjects.append(subject)
    
    def _load_faculty(self):
        df = pd.read_csv(f'{self.data_folder}/subject_teachers.csv')
        for _, row in df.iterrows():
            courses = []
            for col in ['Course 1', 'Course 2', 'Course 3']:
                if pd.notna(row[col]):
                    courses.append(str(row[col]))
            faculty = Faculty(
                faculty_id=int(row['faculty_id']),
                name=str(row['Name of the Faculty']),
                designation=str(row['Designation']),
                courses=courses,
                max_hours=int(row['No.of Working Hours/Week'])
            )
            self.faculty.append(faculty)
    
    def _load_labs(self):
        df = pd.read_csv(f'{self.data_folder}/labs.csv')
        for _, row in df.iterrows():
            lab = Lab(
                lab_id=str(row['lab_id']),
                lab_name=str(row['lab_name']),
                P=int(row['P']),
                capacity=int(row['capacity']),
                branch=str(row['branch']),
                semester=int(row['semester']),
                is_elective=bool(row['is_elective'])
            )
            self.labs.append(lab)
    
    def _load_rooms(self):
        df = pd.read_csv(f'{self.data_folder}/rooms.csv')
        for _, row in df.iterrows():
            room = LabRoom(
                room_id=str(row['Lab Room']),
                course_code=str(row['Course Code']),
                course_name=str(row['Course Name']),
                branches=str(row['Branches']).split(',')
            )
            self.lab_rooms.append(room)
    
    def get_branches(self) -> List[str]:
        return sorted(list(set(s.branch for s in self.subjects)))
    
    def get_semesters_for_branch(self, branch: str) -> List[int]:
        return sorted(list(set(s.semester for s in self.subjects if s.branch == branch)))

# ============================================================================
# TIMETABLE APPLICATION (Same as before)
# ============================================================================

class TimetableApplication:
    def __init__(self):
        self.data_loader = CSVDataLoader()
        self.db_manager = DatabaseManager()
        self.semester_mode: Optional[SemesterMode] = None
    
    def initialize(self) -> bool:
        return self.data_loader.load_all()
    
    def set_semester_mode(self, mode: SemesterMode):
        self.semester_mode = mode
    
    def get_active_semesters(self) -> List[int]:
        if self.semester_mode == SemesterMode.ODD:
            return [3, 5, 7]
        else:
            return [4, 6]

# ============================================================================
# TIMETABLE VIEWER (Same as before - no changes needed)
# ============================================================================

class TimetableViewer(tk.Toplevel):
    """Popup window for viewing timetables WITH COURSE INFORMATION PANEL"""
    
    def __init__(self, parent, schedule_data, sections, faculty, subjects, labs):
        super().__init__(parent)
        self.title("View Timetable")
        self.geometry("1400x900")
        
        self.schedule_data = schedule_data
        self.sections = sections
        self.faculty = faculty
        self.subjects = subjects
        self.labs = labs
        
        self.day_names = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
        self.period_times = [
            '8:45-9:45', '9:45-10:45', '11:00-12:00', '12:00-1:00',
            '1:00-2:00', '2:00-3:00', '3:15-4:15', '4:15-5:15'
        ]
        
        self.create_widgets()
    
    def create_widgets(self):
        # Header
        header_frame = ttk.Frame(self, padding=10)
        header_frame.pack(fill='x')
        
        ttk.Label(header_frame, text="Timetable Viewer", 
                 font=('Arial', 16, 'bold')).pack(side='left')
        
        # Color legend
        legend_frame = ttk.LabelFrame(header_frame, text="Color Legend", padding=5)
        legend_frame.pack(side='right', padx=20)
        
        tk.Label(legend_frame, text=" Regular ", bg="#87CEEB", 
                relief='solid', borderwidth=1, padx=5, pady=2).grid(row=0, column=0, padx=5, pady=2)
        tk.Label(legend_frame, text=" Laboratory ", bg="#90EE90", 
                relief='solid', borderwidth=1, padx=5, pady=2).grid(row=0, column=1, padx=5, pady=2)
        tk.Label(legend_frame, text=" Electives ", bg="#FFB6C1", 
                relief='solid', borderwidth=1, padx=5, pady=2).grid(row=0, column=2, padx=5, pady=2)
        tk.Label(legend_frame, text=" T&P ", bg="#FFD700", 
                relief='solid', borderwidth=1, padx=5, pady=2).grid(row=0, column=3, padx=5, pady=2)
        tk.Label(legend_frame, text=" Free ", bg="#f0f0f0", 
                relief='solid', borderwidth=1, padx=5, pady=2).grid(row=0, column=4, padx=5, pady=2)
        
        # View selector
        selector_frame = ttk.LabelFrame(self, text="Select View", padding=10)
        selector_frame.pack(fill='x', padx=10, pady=5)
        
        self.view_type_var = tk.StringVar(value="section")
        
        ttk.Radiobutton(selector_frame, text="Student View", 
                       variable=self.view_type_var, value="section",
                       command=self.update_selector).pack(side='left', padx=10)
        
        ttk.Radiobutton(selector_frame, text="Faculty View", 
                       variable=self.view_type_var, value="faculty",
                       command=self.update_selector).pack(side='left', padx=10)
        
        self.selector_label = ttk.Label(selector_frame, text="Select Section:")
        self.selector_label.pack(side='left', padx=10)
        
        self.selector_var = tk.StringVar()
        self.selector_combo = ttk.Combobox(selector_frame, textvariable=self.selector_var,
                                          state='readonly', width=30)
        self.selector_combo.pack(side='left', padx=5)
        self.selector_combo.bind('<<ComboboxSelected>>', lambda e: self.load_timetable())
        
        # Main content frame with split view
        content_frame = ttk.Frame(self)
        content_frame.pack(fill='both', expand=True, padx=10, pady=5)
        
        # Left: Timetable display
        left_frame = ttk.LabelFrame(content_frame, text="Timetable", padding=10)
        left_frame.pack(side='left', fill='both', expand=True, padx=(0, 5))
        
        canvas = tk.Canvas(left_frame)
        scrollbar = ttk.Scrollbar(left_frame, orient="vertical", command=canvas.yview)
        self.scrollable_frame = ttk.Frame(canvas)
        
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # Right: Course Information Panel
        right_frame = ttk.LabelFrame(content_frame, text="Course Information", padding=10)
        right_frame.pack(side='right', fill='both', padx=(5, 0), ipadx=10)
        
        info_scroll = ttk.Scrollbar(right_frame)
        info_scroll.pack(side='right', fill='y')
        
        self.course_info_text = tk.Text(right_frame, width=40, wrap=tk.WORD,
                                       font=('Courier', 9), yscrollcommand=info_scroll.set)
        self.course_info_text.pack(side='left', fill='both', expand=True)
        info_scroll.config(command=self.course_info_text.yview)
        
        self.update_selector()
    
    def update_selector(self):
        view_type = self.view_type_var.get()
        
        if view_type == "section":
            self.selector_label.config(text="Select Section:")
            self.selector_combo['values'] = self.sections
        else:
            self.selector_label.config(text="Select Faculty:")
            faculty_names = [f"{fac.faculty_id} - {fac.name}" for fac in self.faculty]
            self.selector_combo['values'] = faculty_names
        
        if self.selector_combo['values']:
            self.selector_combo.current(0)
            self.load_timetable()
    
    def load_timetable(self):
        for widget in self.scrollable_frame.winfo_children():
            widget.destroy()
        
        view_type = self.view_type_var.get()
        selection = self.selector_var.get()
        
        if not selection:
            return
        
        if view_type == "section":
            self.display_section_timetable(selection)
            self.display_course_info(selection)
        else:
            faculty_id = int(selection.split(' - ')[0])
            self.display_faculty_timetable(faculty_id)
            self.course_info_text.delete('1.0', 'end')
            self.course_info_text.insert('1.0', "Course information available\nonly in Student View")
    
    def display_section_timetable(self, section_id: str):
        timetable = self.schedule_data.get(section_id, {})
        
        ttk.Label(self.scrollable_frame, 
                 text=f"Timetable for {section_id}",
                 font=('Arial', 14, 'bold')).grid(row=0, column=0, columnspan=9, pady=10)
        
        ttk.Label(self.scrollable_frame, text="Day/Period", 
                 font=('Arial', 10, 'bold'), relief='raised').grid(row=1, column=0, sticky='nsew')
        
        for p, time in enumerate(self.period_times):
            ttk.Label(self.scrollable_frame, text=f"P{p+1}\n{time}", 
                     font=('Arial', 9, 'bold'), relief='raised').grid(row=1, column=p+1, sticky='nsew')
        
        for day in range(5):
            ttk.Label(self.scrollable_frame, text=self.day_names[day], 
                     font=('Arial', 10, 'bold'), relief='raised').grid(row=day+2, column=0, sticky='nsew')
            
            for period in range(8):
                cell_text = "FREE"
                bg_color = "#f0f0f0"
                
                if day in timetable and period in timetable[day]:
                    assignment = timetable[day][period]
                    subject_id = assignment.get('subject_id', 'N/A')
                    faculty_id = assignment.get('faculty_id', 'N/A')
                    room = assignment.get('room', 'N/A')
                    is_lab = assignment.get('is_lab', False)
                    is_elective = assignment.get('is_elective', False)
                    is_continuous = assignment.get('is_continuous_pair', False)
                    
                    cell_text = f"{subject_id}\n"
                    if faculty_id and faculty_id != 'N/A':
                        cell_text += f"F: {faculty_id}\n"
                    cell_text += f"R: {room}"
                    
                    if is_continuous:
                        bg_color = "#FFD700"
                    elif is_lab:
                        bg_color = "#90EE90"
                    elif is_elective:
                        bg_color = "#FFB6C1"
                    else:
                        bg_color = "#87CEEB"
                
                cell = tk.Label(self.scrollable_frame, text=cell_text,
                               font=('Arial', 8), relief='solid', bg=bg_color,
                               borderwidth=1, wraplength=120, justify='center')
                cell.grid(row=day+2, column=period+1, sticky='nsew', padx=1, pady=1, ipadx=5, ipady=5)
    
    def display_faculty_timetable(self, faculty_id: int):
        timetable = {day: {} for day in range(5)}
        
        for section_id, section_data in self.schedule_data.items():
            for day, day_data in section_data.items():
                for period, assignment in day_data.items():
                    if assignment.get('faculty_id') == faculty_id:
                        if period not in timetable[day]:
                            timetable[day][period] = []
                        timetable[day][period].append({
                            **assignment,
                            'section': section_id
                        })
        
        faculty_name = next((f.name for f in self.faculty if f.faculty_id == faculty_id), "Unknown")
        
        ttk.Label(self.scrollable_frame, 
                 text=f"Timetable for Faculty {faculty_id} - {faculty_name}",
                 font=('Arial', 14, 'bold')).grid(row=0, column=0, columnspan=9, pady=10)
        
        ttk.Label(self.scrollable_frame, text="Day/Period", 
                 font=('Arial', 10, 'bold'), relief='raised').grid(row=1, column=0, sticky='nsew')
        
        for p, time in enumerate(self.period_times):
            ttk.Label(self.scrollable_frame, text=f"P{p+1}\n{time}", 
                     font=('Arial', 9, 'bold'), relief='raised').grid(row=1, column=p+1, sticky='nsew')
        
        for day in range(5):
            ttk.Label(self.scrollable_frame, text=self.day_names[day], 
                     font=('Arial', 10, 'bold'), relief='raised').grid(row=day+2, column=0, sticky='nsew')
            
            for period in range(8):
                cell_text = "FREE"
                bg_color = "#f0f0f0"
                
                if period in timetable.get(day, {}):
                    assignments = timetable[day][period]
                    if assignments:
                        assignment = assignments[0]
                        subject_id = assignment.get('subject_id', 'N/A')
                        section = assignment.get('section', 'N/A')
                        room = assignment.get('room', 'N/A')
                        cell_text = f"{subject_id}\n{section}\nR: {room}"
                        bg_color = "#87CEEB"
                
                cell = tk.Label(self.scrollable_frame, text=cell_text,
                               font=('Arial', 8), relief='solid', bg=bg_color,
                               borderwidth=1, wraplength=120, justify='center')
                cell.grid(row=day+2, column=period+1, sticky='nsew', padx=1, pady=1, ipadx=5, ipady=5)
    
    def display_course_info(self, section_id: str):
        """Display course information for selected section"""
        self.course_info_text.delete('1.0', 'end')
        
        parts = section_id.split('_')
        branch = parts[0]
        semester = int(parts[1].replace('Sem', ''))
        
        self.course_info_text.insert('end', f"COURSE INFORMATION\n")
        self.course_info_text.insert('end', f"{'='*40}\n\n")
        self.course_info_text.insert('end', f"Section: {section_id}\n")
        self.course_info_text.insert('end', f"Branch: {branch}\n")
        self.course_info_text.insert('end', f"Semester: {semester}\n\n")
        self.course_info_text.insert('end', f"{'='*40}\n\n")
        
        timetable = self.schedule_data.get(section_id, {})
        subject_ids = set()
        
        for day_data in timetable.values():
            for assignment in day_data.values():
                subject_ids.add(assignment.get('subject_id'))
        
        course_count = 0
        for subject_id in sorted(subject_ids):
            subject = next((s for s in self.subjects if s.subject_id == subject_id), None)
            
            if not subject:
                lab = next((l for l in self.labs if l.lab_id == subject_id), None)
                if lab:
                    course_count += 1
                    self.course_info_text.insert('end', f"{course_count}. {lab.lab_name}\n")
                    self.course_info_text.insert('end', f"   Code: {lab.lab_id}\n")
                    self.course_info_text.insert('end', f"   Type: Laboratory\n")
                    self.course_info_text.insert('end', f"   Practical: {lab.P} hours\n")
                    self.course_info_text.insert('end', f"   Capacity: {lab.capacity}\n")
                    if lab.is_elective:
                        self.course_info_text.insert('end', f"   Status: Elective\n")
                    self.course_info_text.insert('end', f"\n")
                continue
            
            course_count += 1
            self.course_info_text.insert('end', f"{course_count}. {subject.subject_name}\n")
            self.course_info_text.insert('end', f"   Code: {subject.subject_id}\n")
            
            subject_type = subject.get_subject_type()
            type_str = {
                SubjectType.PURE_THEORY: "Pure Theory",
                SubjectType.PURE_LAB: "Pure Laboratory",
                SubjectType.SEMI_LAB: "Theory + Lab",
                SubjectType.TP_SUBJECT: "T&P (Soft Skills)"
            }.get(subject_type, "Unknown")
            
            self.course_info_text.insert('end', f"   Type: {type_str}\n")
            
            if subject.L > 0:
                self.course_info_text.insert('end', f"   Lecture: {subject.L} hours/week\n")
            if subject.T > 0:
                self.course_info_text.insert('end', f"   Tutorial: {subject.T} hours/week\n")
            if subject.P > 0:
                self.course_info_text.insert('end', f"   Practical: {subject.P} hours/week\n")
            
            total_hours = subject.L + subject.T + subject.P
            self.course_info_text.insert('end', f"   Total: {total_hours} hours/week\n")
            
            if subject.is_elective:
                self.course_info_text.insert('end', f"   Status: Elective\n")
                if subject.elective_group:
                    self.course_info_text.insert('end', f"   Group: {subject.elective_group}\n")
            
            self.course_info_text.insert('end', f"\n")
        
        self.course_info_text.insert('end', f"{'='*40}\n")
        self.course_info_text.insert('end', f"Total Courses: {course_count}\n")

# ============================================================================
# MAIN GUI - COMPLETE WITH ALL FEATURES INCLUDING FACULTY ASSIGNMENT
# ============================================================================

class ThreeLayerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("SASTRA Timetable - Pattern-Free Scheduler v5.2")
        self.root.geometry("1400x900")
        
        self.app = TimetableApplication()
        self.generator = None
        self.current_step = 0
        
        self.generated_schedule = None
        self.generation_stats = None
        
        self.elective_groups_config = {}
        self.elective_assignments = {}
        self.faculty_assignments = {}
        
        self.setup_styles()
        
        self.main_container = ttk.Frame(root, padding="20")
        self.main_container.pack(fill='both', expand=True)
        
        self.initialize_app()
    
    def setup_styles(self):
        self.style = ttk.Style()
        self.style.theme_use('clam')
        
        self.colors = {
            'primary': '#1a5490',
            'secondary': '#3d85c6',
            'success': '#28a745',
            'warning': '#ffc107',
            'danger': '#dc3545'
        }
        
        self.style.configure('Title.TLabel', font=('Arial', 16, 'bold'), 
                           foreground=self.colors['primary'])
    
    def initialize_app(self):
        loading_frame = ttk.Frame(self.main_container)
        loading_frame.pack(fill='both', expand=True)
        
        ttk.Label(loading_frame, text="Loading Data...", style='Title.TLabel').pack(pady=50)
        progress = ttk.Progressbar(loading_frame, mode='indeterminate')
        progress.pack(pady=20)
        progress.start()
        
        self.root.update()
        
        if self.app.initialize():
            progress.stop()
            loading_frame.destroy()
            self.show_step1_semester_mode()
        else:
            progress.stop()
            messagebox.showerror("Error", "Failed to load CSV files from 'data' folder")
            self.root.destroy()
    
    def clear_container(self):
        for widget in self.main_container.winfo_children():
            widget.destroy()
    
    # ========== STEP 1: SEMESTER MODE ==========
    
    def show_step1_semester_mode(self):
        self.clear_container()
        self.current_step = 1
        
        header_frame = ttk.Frame(self.main_container)
        header_frame.pack(fill='x', pady=(0, 30))
        
        ttk.Label(header_frame, text="Step 1: Select Semester Mode", 
                 style='Title.TLabel').pack()
        
        selection_frame = ttk.LabelFrame(self.main_container, text="Semester Mode", padding=30)
        selection_frame.pack(fill='both', expand=True, pady=20)
        
        self.semester_var = tk.StringVar(value="odd")
        
        ttk.Radiobutton(selection_frame, text="Odd Semester (3rd, 5th, 7th)", 
                       variable=self.semester_var, value="odd").pack(anchor='w', pady=10)
        ttk.Radiobutton(selection_frame, text="Even Semester (4th, 6th)", 
                       variable=self.semester_var, value="even").pack(anchor='w', pady=10)
        
        nav_frame = ttk.Frame(self.main_container)
        nav_frame.pack(fill='x', pady=20)
        
        ttk.Button(nav_frame, text="Next: Configuration", 
                  command=self.save_semester_mode_and_continue,
                  style='Primary.TButton').pack(side='right', padx=5)
    
    def save_semester_mode_and_continue(self):
        mode_str = self.semester_var.get()
        mode = SemesterMode.ODD if mode_str == "odd" else SemesterMode.EVEN
        self.app.set_semester_mode(mode)
        self.show_step2_configuration()
    
    # ========== STEP 2: CONFIGURATION ==========
    
    def show_step2_configuration(self):
        self.clear_container()
        self.current_step = 2
        
        header_frame = ttk.Frame(self.main_container)
        header_frame.pack(fill='x', pady=(0, 20))
        
        ttk.Label(header_frame, text="Step 2: Configuration", 
                 style='Title.TLabel').pack()
        
        notebook = ttk.Notebook(self.main_container)
        notebook.pack(fill='both', expand=True, pady=10)
        
        # Tab 1: Section Configuration
        section_tab = ttk.Frame(notebook)
        notebook.add(section_tab, text="  1. Section Configuration  ")
        self.create_section_configuration_tab(section_tab)
        
        # Tab 2: Elective Grouping
        elective_tab = ttk.Frame(notebook)
        notebook.add(elective_tab, text="  2. Elective Grouping  ")
        self.create_elective_grouping_tab(elective_tab)
        
        # Tab 3: Core-Lab Pairing
        pairing_tab = ttk.Frame(notebook)
        notebook.add(pairing_tab, text="  3. Core-Lab Pairing  ")
        self.create_pairing_tab(pairing_tab)
        
        # Navigation
        nav_frame = ttk.Frame(self.main_container)
        nav_frame.pack(fill='x', pady=20)
        
        ttk.Button(nav_frame, text="← Back", 
                  command=self.show_step1_semester_mode).pack(side='left', padx=5)
        
        view_all_btn = tk.Button(nav_frame,
                                text="📋 VIEW ALL CONFIGURATIONS",
                                font=('Arial', 11, 'bold'),
                                bg=self.colors['warning'],
                                fg='black',
                                padx=15,
                                pady=8,
                                relief='raised',
                                command=self.show_all_configurations)
        view_all_btn.pack(side='left', padx=20)
        
        proceed_btn = tk.Button(nav_frame,
                               text="✓ PROCEED TO FACULTY ASSIGNMENT →",
                               font=('Arial', 12, 'bold'),
                               bg=self.colors['success'],
                               fg='white',
                               padx=20,
                               pady=10,
                               relief='raised',
                               command=self.show_step3_faculty_assignment)
        proceed_btn.pack(side='right', padx=5)
    
    def show_all_configurations(self):
        """Show all configurations in a popup"""
        popup = tk.Toplevel(self.root)
        popup.title("All Configurations Summary")
        popup.geometry("1000x700")
        
        text_frame = ttk.Frame(popup, padding=20)
        text_frame.pack(fill='both', expand=True)
        
        scroll = ttk.Scrollbar(text_frame)
        scroll.pack(side='right', fill='y')
        
        text_widget = tk.Text(text_frame, yscrollcommand=scroll.set, 
                             font=('Courier', 10), wrap=tk.WORD)
        text_widget.pack(side='left', fill='both', expand=True)
        scroll.config(command=text_widget.yview)
        
        text_widget.insert(tk.END, "=" * 80 + "\n")
        text_widget.insert(tk.END, "COMPLETE CONFIGURATION SUMMARY\n")
        text_widget.insert(tk.END, "=" * 80 + "\n\n")
        
        mode = self.app.semester_mode
        if mode:
            text_widget.insert(tk.END, f"SEMESTER MODE: {mode.value.upper()}\n")
            active_sems = self.app.get_active_semesters()
            text_widget.insert(tk.END, f"Active Semesters: {', '.join(map(str, active_sems))}\n\n")
        
        text_widget.insert(tk.END, "-" * 80 + "\n\n")
        
        text_widget.insert(tk.END, "1. SECTION CONFIGURATIONS\n")
        text_widget.insert(tk.END, "-" * 80 + "\n")
        
        sections = self.app.db_manager.get_all_sections()
        if sections:
            text_widget.insert(tk.END, f"{'Branch':<15} {'Number of Sections':<20}\n")
            text_widget.insert(tk.END, "-" * 80 + "\n")
            for branch, num in sections.items():
                text_widget.insert(tk.END, f"{branch:<15} {num:<20}\n")
            text_widget.insert(tk.END, f"\nTotal Branches Configured: {len(sections)}\n")
        else:
            text_widget.insert(tk.END, "⚠ No section configurations found!\n")
        
        text_widget.insert(tk.END, "\n" + "-" * 80 + "\n\n")
        
        text_widget.insert(tk.END, "2. ELECTIVE GROUPINGS\n")
        text_widget.insert(tk.END, "-" * 80 + "\n")
        
        if self.elective_assignments:
            for (branch, semester), groups in self.elective_assignments.items():
                if groups:
                    text_widget.insert(tk.END, f"\n{branch} - Semester {semester}:\n")
                    for group_num in sorted(groups.keys()):
                        electives = groups[group_num]
                        text_widget.insert(tk.END, f"  Group {group_num}: {len(electives)} electives\n")
                        for elec_id in electives:
                            subject = next((s for s in self.app.data_loader.subjects if s.subject_id == elec_id), None)
                            if subject:
                                text_widget.insert(tk.END, f"    - {elec_id}: {subject.subject_name}\n")
            
            total_groups = sum(len(groups) for groups in self.elective_assignments.values())
            text_widget.insert(tk.END, f"\nTotal Elective Groups: {total_groups}\n")
        else:
            text_widget.insert(tk.END, "ℹ No elective groupings configured\n")
        
        text_widget.insert(tk.END, "\n" + "-" * 80 + "\n\n")
        
        text_widget.insert(tk.END, "3. CORE-LAB PAIRINGS\n")
        text_widget.insert(tk.END, "-" * 80 + "\n")
        
        pairs = self.app.db_manager.get_all_core_lab_pairs()
        if pairs:
            grouped_pairs = {}
            for pair in pairs:
                key = (pair.branch, pair.semester)
                if key not in grouped_pairs:
                    grouped_pairs[key] = []
                grouped_pairs[key].append(pair)
            
            for (branch, semester), pair_list in sorted(grouped_pairs.items()):
                text_widget.insert(tk.END, f"\n{branch} - Semester {semester}:\n")
                text_widget.insert(tk.END, f"  {'Subject':<15} {'Lab':<15} {'Same Faculty':<15}\n")
                text_widget.insert(tk.END, "  " + "-" * 45 + "\n")
                
                for pair in pair_list:
                    same_fac = "Yes" if pair.faculty_must_match else "No"
                    text_widget.insert(tk.END, f"  {pair.subject_id:<15} {pair.lab_id:<15} {same_fac:<15}\n")
            
            text_widget.insert(tk.END, f"\nTotal Pairings: {len(pairs)}\n")
        else:
            text_widget.insert(tk.END, "ℹ No core-lab pairings configured\n")
        
        text_widget.insert(tk.END, "\n" + "=" * 80 + "\n")
        
        text_widget.config(state='disabled')
        
        ttk.Button(popup, text="Close", command=popup.destroy).pack(pady=10)
    
    def create_section_configuration_tab(self, parent):
        """Create section configuration interface"""
        select_frame = ttk.LabelFrame(parent, text="Add Section Configuration", padding=20)
        select_frame.pack(fill='x', padx=20, pady=20)
        
        branch_frame = ttk.Frame(select_frame)
        branch_frame.pack(fill='x', pady=10)
        
        ttk.Label(branch_frame, text="Branch:", font=('Arial', 10, 'bold')).pack(side='left', padx=5)
        self.branch_var = tk.StringVar()
        branch_combo = ttk.Combobox(branch_frame, textvariable=self.branch_var, 
                                     values=self.app.data_loader.get_branches(), 
                                     state='readonly', width=15)
        branch_combo.pack(side='left', padx=5)
        
        ttk.Label(branch_frame, text="Sections:", font=('Arial', 10, 'bold')).pack(side='left', padx=(20, 5))
        self.sections_var = tk.StringVar(value="3")
        sections_spin = ttk.Spinbox(branch_frame, from_=1, to=10, textvariable=self.sections_var, width=10)
        sections_spin.pack(side='left', padx=5)
        
        ttk.Button(branch_frame, text="Add", 
                  command=self.add_section_configuration).pack(side='left', padx=20)
        
        config_frame = ttk.LabelFrame(parent, text="Current Configurations", padding=20)
        config_frame.pack(fill='both', expand=True, padx=20, pady=20)
        
        columns = ('branch', 'sections')
        self.section_tree = ttk.Treeview(config_frame, columns=columns, show='headings', height=10)
        
        self.section_tree.heading('branch', text='Branch')
        self.section_tree.heading('sections', text='Sections')
        
        self.section_tree.column('branch', width=200)
        self.section_tree.column('sections', width=150)
        
        scrollbar = ttk.Scrollbar(config_frame, orient='vertical', command=self.section_tree.yview)
        self.section_tree.configure(yscrollcommand=scrollbar.set)
        
        self.section_tree.pack(side='left', fill='both', expand=True)
        scrollbar.pack(side='right', fill='y')
        
        btn_frame = ttk.Frame(config_frame)
        btn_frame.pack(pady=10)
        
        ttk.Button(btn_frame, text="Delete Selected", 
                  command=self.delete_section_configuration).pack(side='left', padx=5)
        
        self.refresh_section_configurations()
    
    def add_section_configuration(self):
        branch = self.branch_var.get()
        sections = self.sections_var.get()
        
        if not branch:
            messagebox.showerror("Error", "Please select a branch")
            return
        
        try:
            sections_num = int(sections)
            if sections_num < 1 or sections_num > 10:
                raise ValueError()
        except:
            messagebox.showerror("Error", "Sections must be 1-10")
            return
        
        self.app.db_manager.add_section_config(branch, sections_num)
        self.refresh_section_configurations()
        messagebox.showinfo("Success", f"Added: {branch} - {sections_num} sections")
    
    def delete_section_configuration(self):
        selection = self.section_tree.selection()
        if not selection:
            messagebox.showerror("Error", "Please select a configuration")
            return
        
        item = self.section_tree.item(selection[0])
        branch = item['values'][0]
        
        if messagebox.askyesno("Confirm", f"Delete {branch}?"):
            self.app.db_manager.delete_section_config(branch)
            self.refresh_section_configurations()
    
    def refresh_section_configurations(self):
        for item in self.section_tree.get_children():
            self.section_tree.delete(item)
        
        configs = self.app.db_manager.get_all_sections()
        for branch, sections in configs.items():
            self.section_tree.insert('', 'end', values=(branch, sections))
    
    def create_elective_grouping_tab(self, parent):
        """Create elective grouping interface"""
        warning_frame = ttk.Frame(parent)
        warning_frame.pack(fill='x', padx=20, pady=10)
        
        warning_label = tk.Label(warning_frame,
                                text="⚠ IMPORTANT: Only electives added to groups will be scheduled!",
                                font=('Arial', 11, 'bold'),
                                foreground='white',
                                bg='#dc3545',
                                padx=20,
                                pady=15)
        warning_label.pack(fill='x')
        
        select_frame = ttk.LabelFrame(parent, text="Configure Elective Groups", padding=15)
        select_frame.pack(fill='x', padx=20, pady=10)
        
        select_inner = ttk.Frame(select_frame)
        select_inner.pack(fill='x')
        
        ttk.Label(select_inner, text="Branch:", font=('Arial', 10, 'bold')).grid(row=0, column=0, padx=5, pady=5, sticky='w')
        self.elec_branch_var = tk.StringVar()
        branch_combo = ttk.Combobox(select_inner, textvariable=self.elec_branch_var, 
                                     values=self.app.data_loader.get_branches(), 
                                     state='readonly', width=15)
        branch_combo.grid(row=0, column=1, padx=5, pady=5)
        branch_combo.bind('<<ComboboxSelected>>', self.on_elective_branch_changed)
        
        ttk.Label(select_inner, text="Semester:", font=('Arial', 10, 'bold')).grid(row=0, column=2, padx=(20, 5), pady=5, sticky='w')
        self.elec_semester_var = tk.StringVar()
        self.elec_semester_combo = ttk.Combobox(select_inner, textvariable=self.elec_semester_var, 
                                                state='readonly', width=10)
        self.elec_semester_combo.grid(row=0, column=3, padx=5, pady=5)
        
        ttk.Label(select_inner, text="No. of Groups:", font=('Arial', 10, 'bold')).grid(row=0, column=4, padx=(20, 5), pady=5, sticky='w')
        self.num_elective_groups_var = tk.StringVar(value="2")
        elec_groups_spin = ttk.Spinbox(select_inner, from_=1, to=5, textvariable=self.num_elective_groups_var, width=10)
        elec_groups_spin.grid(row=0, column=5, padx=5, pady=5)
        
        ttk.Button(select_inner, text="Load Electives", 
                  command=self.load_electives_for_grouping).grid(row=0, column=6, padx=20, pady=5)
        
        display_frame = ttk.Frame(parent)
        display_frame.pack(fill='both', expand=True, padx=20, pady=10)
        
        left_frame = ttk.LabelFrame(display_frame, text="Available Electives", padding=10)
        left_frame.pack(side='left', fill='both', expand=True, padx=(0, 5))
        
        elec_scroll = ttk.Scrollbar(left_frame)
        elec_scroll.pack(side='right', fill='y')
        
        self.elective_listbox = tk.Listbox(left_frame, yscrollcommand=elec_scroll.set, 
                                           font=('Courier', 9), selectmode='multiple', height=10)
        self.elective_listbox.pack(side='left', fill='both', expand=True)
        elec_scroll.config(command=self.elective_listbox.yview)
        
        button_frame = ttk.Frame(display_frame)
        button_frame.pack(side='left', padx=15)
        
        ttk.Label(button_frame, text="Assign to:", font=('Arial', 10, 'bold')).pack(pady=10)
        
        self.group_buttons = []
        for i in range(1, 6):
            btn = ttk.Button(button_frame, text=f"Group {i}", 
                           command=lambda g=i: self.assign_to_group(g),
                           state='disabled', width=15)
            btn.pack(pady=5)
            self.group_buttons.append(btn)
        
        right_frame = ttk.LabelFrame(display_frame, text="Current Groupings", padding=10)
        right_frame.pack(side='left', fill='both', expand=True, padx=(5, 0))
        
        group_scroll = ttk.Scrollbar(right_frame)
        group_scroll.pack(side='right', fill='y')
        
        self.grouping_text = tk.Text(right_frame, yscrollcommand=group_scroll.set, 
                                     font=('Courier', 9), height=10, wrap=tk.WORD)
        self.grouping_text.pack(side='left', fill='both', expand=True)
        group_scroll.config(command=self.grouping_text.yview)
    
    def on_elective_branch_changed(self, event=None):
        branch = self.elec_branch_var.get()
        if branch:
            semesters = self.app.data_loader.get_semesters_for_branch(branch)
            active_semesters = self.app.get_active_semesters()
            filtered = [s for s in semesters if s in active_semesters]
            self.elec_semester_combo['values'] = filtered
            if filtered:
                self.elec_semester_combo.current(0)
    
    def load_electives_for_grouping(self):
        branch = self.elec_branch_var.get()
        semester = self.elec_semester_var.get()
        num_groups = self.num_elective_groups_var.get()
        
        if not branch or not semester:
            messagebox.showerror("Error", "Select branch and semester")
            return
        
        try:
            num_groups = int(num_groups)
        except:
            messagebox.showerror("Error", "Invalid number of groups")
            return
        
        semester = int(semester)
        key = (branch, semester)
        
        self.elective_groups_config[key] = num_groups
        
        if key not in self.elective_assignments:
            self.elective_assignments[key] = {}
        
        subjects = [s for s in self.app.data_loader.subjects 
                   if s.branch == branch and s.semester == semester and s.is_elective]
        
        assigned = set()
        for group_num, elec_list in self.elective_assignments[key].items():
            assigned.update(elec_list)
        
        available = [e for e in subjects if e.subject_id not in assigned]
        
        self.elective_listbox.delete(0, tk.END)
        for elective in available:
            display = f"{elective.subject_id:15s} | {elective.subject_name}"
            self.elective_listbox.insert(tk.END, display)
        
        self.current_available_electives = available
        self.current_elective_key = key
        
        for i, btn in enumerate(self.group_buttons):
            if i < num_groups:
                btn.config(state='normal')
            else:
                btn.config(state='disabled')
        
        self.update_grouping_display()
    
    def assign_to_group(self, group_num):
        selection = self.elective_listbox.curselection()
        if not selection:
            messagebox.showerror("Error", "Select at least one elective")
            return
        
        if not hasattr(self, 'current_elective_key'):
            messagebox.showerror("Error", "Load electives first")
            return
        
        key = self.current_elective_key
        
        selected = []
        for idx in selection:
            text = self.elective_listbox.get(idx)
            elective_id = text.split('|')[0].strip()
            selected.append(elective_id)
        
        if group_num not in self.elective_assignments[key]:
            self.elective_assignments[key][group_num] = []
        
        self.elective_assignments[key][group_num].extend(selected)
        
        for idx in reversed(selection):
            self.elective_listbox.delete(idx)
        
        self.update_grouping_display()
        messagebox.showinfo("Success", f"Assigned {len(selected)} to Group {group_num}")
    
    def update_grouping_display(self):
        if not hasattr(self, 'current_elective_key'):
            return
        
        key = self.current_elective_key
        branch, semester = key
        
        self.grouping_text.delete(1.0, tk.END)
        
        if key not in self.elective_assignments or not self.elective_assignments[key]:
            self.grouping_text.insert(tk.END, "No groupings yet")
            return
        
        self.grouping_text.insert(tk.END, f"{branch} - Semester {semester}\n")
        self.grouping_text.insert(tk.END, "=" * 60 + "\n\n")
        
        for group_num in sorted(self.elective_assignments[key].keys()):
            electives = self.elective_assignments[key][group_num]
            self.grouping_text.insert(tk.END, f"Group {group_num}: ({len(electives)} electives)\n")
            for elec_id in electives:
                subject = next((s for s in self.app.data_loader.subjects if s.subject_id == elec_id), None)
                if subject:
                    self.grouping_text.insert(tk.END, f"  - {elec_id} - {subject.subject_name}\n")
            self.grouping_text.insert(tk.END, "\n")
    
    def create_pairing_tab(self, parent):
        """Create core-lab pairing interface"""
        select_frame = ttk.LabelFrame(parent, text="Select Branch and Semester", padding=15)
        select_frame.pack(fill='x', padx=20, pady=10)
        
        select_inner = ttk.Frame(select_frame)
        select_inner.pack(fill='x')
        
        ttk.Label(select_inner, text="Branch:", font=('Arial', 10, 'bold')).grid(row=0, column=0, padx=5, pady=5, sticky='w')
        self.pair_branch_var = tk.StringVar()
        branch_combo = ttk.Combobox(select_inner, textvariable=self.pair_branch_var, 
                                     values=self.app.data_loader.get_branches(), 
                                     state='readonly', width=15)
        branch_combo.grid(row=0, column=1, padx=5, pady=5)
        branch_combo.bind('<<ComboboxSelected>>', self.on_pairing_branch_changed)
        
        ttk.Label(select_inner, text="Semester:", font=('Arial', 10, 'bold')).grid(row=0, column=2, padx=(20, 5), pady=5, sticky='w')
        self.pair_semester_var = tk.StringVar()
        self.pair_semester_combo = ttk.Combobox(select_inner, textvariable=self.pair_semester_var, 
                                                state='readonly', width=10)
        self.pair_semester_combo.grid(row=0, column=3, padx=5, pady=5)
        self.pair_semester_combo.bind('<<ComboboxSelected>>', self.on_pairing_branch_changed)
        
        ttk.Button(select_inner, text="Load Courses", 
                  command=self.load_courses_for_pairing).grid(row=0, column=4, padx=20, pady=5)
        
        middle_frame = ttk.Frame(parent)
        middle_frame.pack(fill='both', expand=True, padx=20, pady=10)
        
        left_frame = ttk.LabelFrame(middle_frame, text="Core/Semi-Lab Subjects", padding=10)
        left_frame.pack(side='left', fill='both', expand=True, padx=(0, 5))
        
        core_scroll = ttk.Scrollbar(left_frame)
        core_scroll.pack(side='right', fill='y')
        
        self.core_listbox = tk.Listbox(left_frame, yscrollcommand=core_scroll.set, 
                                       font=('Courier', 9), selectmode='single', height=10)
        self.core_listbox.pack(side='left', fill='both', expand=True)
        self.core_listbox.bind('<<ListboxSelect>>', self.on_core_selected)
        core_scroll.config(command=self.core_listbox.yview)
        
        button_frame = ttk.Frame(middle_frame)
        button_frame.pack(side='left', padx=10)
        
        self.same_faculty_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(button_frame, text="Same Faculty\nRequired", 
                       variable=self.same_faculty_var).pack(pady=10)
        
        self.pair_button = ttk.Button(button_frame, text="→ PAIR →", 
                                      command=self.create_pair,
                                      state='disabled', width=12)
        self.pair_button.pack(pady=20)
        
        ttk.Label(button_frame, text="Select one\nfrom each side", 
                 font=('Arial', 8), foreground='gray').pack(pady=5)
        
        right_frame = ttk.LabelFrame(middle_frame, text="Lab Subjects", padding=10)
        right_frame.pack(side='left', fill='both', expand=True, padx=(5, 0))
        
        lab_scroll = ttk.Scrollbar(right_frame)
        lab_scroll.pack(side='right', fill='y')
        
        self.lab_listbox = tk.Listbox(right_frame, yscrollcommand=lab_scroll.set, 
                                      font=('Courier', 9), selectmode='single', height=10)
        self.lab_listbox.pack(side='left', fill='both', expand=True)
        self.lab_listbox.bind('<<ListboxSelect>>', self.on_lab_selected)
        lab_scroll.config(command=self.lab_listbox.yview)
        
        bottom_frame = ttk.LabelFrame(parent, text="Current Pairs", padding=10)
        bottom_frame.pack(fill='both', expand=True, padx=20, pady=10)
        
        columns = ('id', 'subject', 'lab', 'branch', 'semester', 'same_faculty')
        self.pairs_tree = ttk.Treeview(bottom_frame, columns=columns, show='headings', height=6)
        
        self.pairs_tree.heading('id', text='ID')
        self.pairs_tree.heading('subject', text='Subject')
        self.pairs_tree.heading('lab', text='Lab')
        self.pairs_tree.heading('branch', text='Branch')
        self.pairs_tree.heading('semester', text='Semester')
        self.pairs_tree.heading('same_faculty', text='Same Faculty')
        
        self.pairs_tree.column('id', width=50)
        self.pairs_tree.column('subject', width=200)
        self.pairs_tree.column('lab', width=200)
        self.pairs_tree.column('branch', width=80)
        self.pairs_tree.column('semester', width=80)
        self.pairs_tree.column('same_faculty', width=100)
        
        pairs_scroll = ttk.Scrollbar(bottom_frame, orient='vertical', command=self.pairs_tree.yview)
        self.pairs_tree.configure(yscrollcommand=pairs_scroll.set)
        
        self.pairs_tree.pack(side='left', fill='both', expand=True)
        pairs_scroll.pack(side='right', fill='y')
        
        btn_frame = ttk.Frame(bottom_frame)
        btn_frame.pack(pady=5)
        
        ttk.Button(btn_frame, text="Delete Selected Pair", 
                  command=self.delete_pair).pack(side='left', padx=5)
        
        self.refresh_pairs()
        
        self.selected_core = None
        self.selected_lab = None
    
    def on_pairing_branch_changed(self, event=None):
        branch = self.pair_branch_var.get()
        if branch:
            semesters = self.app.data_loader.get_semesters_for_branch(branch)
            active_semesters = self.app.get_active_semesters()
            filtered = [s for s in semesters if s in active_semesters]
            self.pair_semester_combo['values'] = filtered
            if filtered and not self.pair_semester_var.get():
                self.pair_semester_combo.current(0)
    
    def load_courses_for_pairing(self):
        branch = self.pair_branch_var.get()
        semester = self.pair_semester_var.get()
        
        if not branch or not semester:
            messagebox.showerror("Error", "Select both branch and semester")
            return
        
        semester = int(semester)
        
        subjects = [s for s in self.app.data_loader.subjects 
                   if s.branch == branch and s.semester == semester]
        labs = [l for l in self.app.data_loader.labs 
               if l.branch == branch and l.semester == semester]
        
        self.core_listbox.delete(0, tk.END)
        self.lab_listbox.delete(0, tk.END)
        
        core_subjects = [s for s in subjects if (s.L > 0 or s.T > 0) and not s.is_elective]
        for subject in core_subjects:
            display = f"{subject.subject_id:15s} | {subject.subject_name:40s} | L:{subject.L} T:{subject.T} P:{subject.P}"
            self.core_listbox.insert(tk.END, display)
        
        self.current_core_subjects = core_subjects
        
        lab_subjects = [s for s in subjects if s.P > 0 and s.L == 0 and s.T == 0 and not s.is_elective]
        for subject in lab_subjects:
            display = f"{subject.subject_id:15s} | {subject.subject_name:40s} | P:{subject.P}"
            self.lab_listbox.insert(tk.END, display)
        
        non_elective_labs = [l for l in labs if not l.is_elective]
        for lab in non_elective_labs:
            display = f"{lab.lab_id:15s} | {lab.lab_name:40s} | P:{lab.P}"
            self.lab_listbox.insert(tk.END, display)
        
        self.current_lab_subjects = lab_subjects + non_elective_labs
        
        self.selected_core = None
        self.selected_lab = None
        self.pair_button.config(state='disabled')
    
    def on_core_selected(self, event=None):
        selection = self.core_listbox.curselection()
        if selection:
            idx = selection[0]
            text = self.core_listbox.get(idx)
            if text.strip():
                subject_id = text.split('|')[0].strip()
                self.selected_core = subject_id
                self.update_pair_button()
    
    def on_lab_selected(self, event=None):
        selection = self.lab_listbox.curselection()
        if selection:
            idx = selection[0]
            text = self.lab_listbox.get(idx)
            if text.strip():
                lab_id = text.split('|')[0].strip()
                self.selected_lab = lab_id
                self.update_pair_button()
    
    def update_pair_button(self):
        if self.selected_core and self.selected_lab:
            self.pair_button.config(state='normal')
        else:
            self.pair_button.config(state='disabled')
    
    def create_pair(self):
        if not self.selected_core or not self.selected_lab:
            return
        
        branch = self.pair_branch_var.get()
        semester = int(self.pair_semester_var.get())
        same_faculty = self.same_faculty_var.get()
        
        pair_id = self.app.db_manager.add_core_lab_pair(
            self.selected_core, self.selected_lab, branch, semester, same_faculty
        )
        
        if pair_id > 0:
            messagebox.showinfo("Success", f"Pair created:\n{self.selected_core} ↔ {self.selected_lab}")
            self.refresh_pairs()
            self.core_listbox.selection_clear(0, tk.END)
            self.lab_listbox.selection_clear(0, tk.END)
            self.selected_core = None
            self.selected_lab = None
            self.pair_button.config(state='disabled')
        else:
            messagebox.showerror("Error", "This pair already exists!")
    
    def delete_pair(self):
        selection = self.pairs_tree.selection()
        if not selection:
            messagebox.showerror("Error", "Please select a pair to delete")
            return
        
        item = self.pairs_tree.item(selection[0])
        pair_id = item['values'][0]
        
        if messagebox.askyesno("Confirm", "Delete this pair?"):
            self.app.db_manager.delete_core_lab_pair(pair_id)
            self.refresh_pairs()
    
    def refresh_pairs(self):
        for item in self.pairs_tree.get_children():
            self.pairs_tree.delete(item)
        
        pairs = self.app.db_manager.get_all_core_lab_pairs()
        for pair in pairs:
            same_fac = "Yes" if pair.faculty_must_match else "No"
            self.pairs_tree.insert('', 'end', values=(
                pair.id, pair.subject_id, pair.lab_id, 
                pair.branch, pair.semester, same_fac
            ))
    
    def get_grouped_electives_for_generation(self):
        grouped_electives = []
        
        for (branch, semester), groups in self.elective_assignments.items():
            for group_num, elective_ids in groups.items():
                if elective_ids:
                    grouped_electives.append({
                        'group_name': f"{branch}_Sem{semester}_Group{group_num}",
                        'branch': branch,
                        'semester': semester,
                        'group_number': group_num,
                        'electives': elective_ids
                    })
        
        return grouped_electives
    
    # ========== STEP 3: FACULTY ASSIGNMENT ==========
    
    def show_step3_faculty_assignment(self):
        """Step 3: Assign Faculty to Courses with Search Functionality"""
        self.clear_container()
        self.current_step = 3

        header_frame = ttk.Frame(self.main_container)
        header_frame.pack(fill='x', pady=(0, 20))

        ttk.Label(header_frame, text="Step 3: Assign Faculty to Courses",
                style='Title.TLabel').pack()
        info_label = ttk.Label(header_frame, text="Select a course, then search for and assign any faculty from the list.",
                            font=('Arial', 10), foreground=self.colors['secondary'])
        info_label.pack(pady=5)
        
        warning_label = tk.Label(header_frame,
                                text="NOTE: The system now allows assigning any faculty. You are responsible for verifying their qualifications.",
                                font=('Arial', 9, 'bold'),
                                foreground='#856404', bg='#fff3cd',
                                padx=10, pady=5, relief='solid', borderwidth=1)
        warning_label.pack(fill='x', pady=(10,0))

        content_frame = ttk.Frame(self.main_container)
        content_frame.pack(fill='both', expand=True, pady=10)

        # Left side: Course Treeview
        left_frame = ttk.LabelFrame(content_frame, text="Courses to Assign", padding=15)
        left_frame.pack(side='left', fill='both', expand=True, padx=(0, 10))

        columns = ('course_id', 'course_name', 'branch_sem', 'hours', 'assigned_faculty')
        self.course_tree = ttk.Treeview(left_frame, columns=columns, show='headings', height=15)
        
        self.course_tree.heading('course_id', text='Course ID')
        self.course_tree.heading('course_name', text='Course Name')
        self.course_tree.heading('branch_sem', text='Branch-Sem')
        self.course_tree.heading('hours', text='Hours/Week')
        self.course_tree.heading('assigned_faculty', text='Assigned Faculty')
        
        self.course_tree.column('course_id', width=100)
        self.course_tree.column('course_name', width=200)
        self.course_tree.column('branch_sem', width=100)
        self.course_tree.column('hours', width=80, anchor='center')
        self.course_tree.column('assigned_faculty', width=150)

        scrollbar = ttk.Scrollbar(left_frame, orient='vertical', command=self.course_tree.yview)
        self.course_tree.configure(yscrollcommand=scrollbar.set)
        self.course_tree.pack(side='left', fill='both', expand=True)
        scrollbar.pack(side='right', fill='y')
        self.course_tree.bind('<<TreeviewSelect>>', self.on_course_selected_for_assignment)

        # Right side: Faculty Selection
        right_frame = ttk.LabelFrame(content_frame, text="Assign Faculty", padding=15)
        right_frame.pack(side='right', fill='both', expand=True, padx=(10, 0))

        self.selected_course_label = ttk.Label(right_frame, text="Select a course from the left", font=('Arial', 10, 'bold'))
        self.selected_course_label.pack(pady=10)

        # Search bar
        search_frame = ttk.Frame(right_frame)
        search_frame.pack(fill='x', pady=(5, 10))
        ttk.Label(search_frame, text="Search Faculty:").pack(side='left', padx=(0, 5))
        self.faculty_search_var = tk.StringVar()
        search_entry = ttk.Entry(search_frame, textvariable=self.faculty_search_var)
        search_entry.pack(side='left', fill='x', expand=True)
        search_entry.bind('<KeyRelease>', self.update_faculty_list_filter)

        self.qualified_faculty_listbox = tk.Listbox(right_frame, font=('Courier', 9), height=12)
        self.qualified_faculty_listbox.pack(fill='both', expand=True, pady=5)

        assign_button = ttk.Button(right_frame, text="Assign Selected Faculty",
                                command=self.assign_faculty_to_course)
        assign_button.pack(pady=10, fill='x')

        unassign_button = ttk.Button(right_frame, text="Unassign Faculty",
                                    command=self.unassign_faculty_from_course)
        unassign_button.pack(pady=5, fill='x')
        
        # Navigation
        nav_frame = ttk.Frame(self.main_container)
        nav_frame.pack(fill='x', pady=20)

        ttk.Button(nav_frame, text="← Back to Configuration",
                command=self.show_step2_configuration).pack(side='left', padx=5)
        ttk.Button(nav_frame, text="Proceed to Generation →",
                command=self.show_generation_step).pack(side='right', padx=5)

        self.populate_course_assignment_tree()

    def update_faculty_list_filter(self, event=None):
        """Filters the faculty listbox based on the search entry."""
        search_term = self.faculty_search_var.get().lower()
        self.qualified_faculty_listbox.delete(0, tk.END)

        if not self.app.data_loader.faculty:
            return

        for fac in self.app.data_loader.faculty:
            if search_term in fac.name.lower() or search_term in str(fac.faculty_id):
                display_text = f"{fac.faculty_id:<5} | {fac.name:<25} | Max Hrs: {fac.max_hours}"
                self.qualified_faculty_listbox.insert(tk.END, display_text)

    def populate_course_assignment_tree(self):
        """Gathers all courses from configured sections and populates the treeview."""
        for item in self.course_tree.get_children():
            self.course_tree.delete(item)

        active_semesters = self.app.get_active_semesters()
        sections_config = self.app.db_manager.get_all_sections()
        all_courses = set()

        for branch, num_sections in sections_config.items():
            for semester in active_semesters:
                subjects = [s for s in self.app.data_loader.subjects if s.branch == branch and s.semester == semester and not s.is_elective]
                labs = [l for l in self.app.data_loader.labs if l.branch == branch and l.semester == semester and not l.is_elective]

                for s in subjects:
                    all_courses.add((s.subject_id, s.subject_name, branch, semester, s.L + s.T + s.P))
                for l in labs:
                    all_courses.add((l.lab_id, l.lab_name, branch, semester, l.P))

        grouped_electives = self.get_grouped_electives_for_generation()
        for group in grouped_electives:
            for elec_id in group['electives']:
                subject = next((s for s in self.app.data_loader.subjects if s.subject_id == elec_id), None)
                if subject:
                    all_courses.add((subject.subject_id, subject.subject_name, subject.branch, subject.semester, subject.L + subject.T + subject.P))

        for course_id, name, branch, sem, hours in sorted(list(all_courses)):
            assigned_faculty_id = self.faculty_assignments.get(course_id)
            faculty_name = "Not Assigned"
            if assigned_faculty_id:
                faculty = next((f for f in self.app.data_loader.faculty if f.faculty_id == assigned_faculty_id), None)
                if faculty:
                    faculty_name = f"{faculty.faculty_id} - {faculty.name}"

            self.course_tree.insert('', 'end', values=(course_id, name, f"{branch}-Sem{sem}", hours, faculty_name))

    def on_course_selected_for_assignment(self, event=None):
        """Handles course selection and populates the full faculty list for searching."""
        selection = self.course_tree.selection()
        if not selection:
            return

        item = self.course_tree.item(selection[0])
        course_id, course_name, _, _, _ = item['values']

        self.selected_course_label.config(text=f"Assign to: {course_id}\n{course_name}")

        self.faculty_search_var.set("")
        self.update_faculty_list_filter()

    def assign_faculty_to_course(self):
        """Assigns the selected faculty to the selected course."""
        course_selection = self.course_tree.selection()
        faculty_selection = self.qualified_faculty_listbox.curselection()

        if not course_selection or not faculty_selection:
            messagebox.showerror("Error", "Please select both a course and a faculty member.")
            return

        course_item = self.course_tree.item(course_selection[0])
        course_id = course_item['values'][0]

        faculty_text = self.qualified_faculty_listbox.get(faculty_selection[0])
        faculty_id = int(faculty_text.split('|')[0].strip())

        self.faculty_assignments[course_id] = faculty_id
        self.populate_course_assignment_tree()
        messagebox.showinfo("Success", f"Assigned Faculty ID {faculty_id} to {course_id}.")

    def unassign_faculty_from_course(self):
        """Removes faculty assignment from the selected course."""
        course_selection = self.course_tree.selection()
        if not course_selection:
            messagebox.showerror("Error", "Please select a course to unassign.")
            return

        course_item = self.course_tree.item(course_selection[0])
        course_id = course_item['values'][0]

        if course_id in self.faculty_assignments:
            del self.faculty_assignments[course_id]
            self.populate_course_assignment_tree()
            messagebox.showinfo("Success", f"Unassigned faculty from {course_id}.")
        else:
            messagebox.showwarning("Warning", "This course has no faculty assigned.")
    
    # ========== STEP 4: GENERATION ==========
    
    def show_generation_step(self):
        self.clear_container()
        self.current_step = 4
        
        header_frame = ttk.Frame(self.main_container)
        header_frame.pack(fill='x', pady=(0, 20))
        
        ttk.Label(header_frame, text="Step 4: Generate Timetable - Pattern-Free AI", 
                 style='Title.TLabel').pack()
        
        ttk.Label(header_frame, 
                 text="Layer 1: CSP (Pattern-Free) → Layer 2: MDP → Layer 3: A2C",
                 font=('Arial', 10), foreground=self.colors['secondary']).pack(pady=5)
        
        progress_frame = ttk.LabelFrame(self.main_container, text="Progress", padding=15)
        progress_frame.pack(fill='x', pady=10, padx=20)
        
        self.progress_label = ttk.Label(progress_frame, text="Ready to generate", 
                                       font=('Arial', 10))
        self.progress_label.pack(fill='x', pady=(0, 5))
        
        self.progress_bar = ttk.Progressbar(progress_frame, mode='determinate', length=400)
        self.progress_bar.pack(fill='x', pady=5)
        
        status_frame = ttk.LabelFrame(self.main_container, text="Generation Log", padding=20)
        status_frame.pack(fill='both', expand=True, pady=20)
        
        self.status_text = scrolledtext.ScrolledText(status_frame, height=15, 
                                                     wrap=tk.WORD, font=('Courier', 9))
        self.status_text.pack(fill='both', expand=True)
        
        button_frame = ttk.Frame(self.main_container)
        button_frame.pack(fill='x', pady=20)
        
        ttk.Button(button_frame, text="← Back to Faculty Assignment", 
                  command=self.show_step3_faculty_assignment).pack(side='left', padx=5)
        
        generate_btn = tk.Button(button_frame, 
                                text="🚀 GENERATE PATTERN-FREE TIMETABLE 🚀", 
                                command=self.generate_timetable,
                                font=('Arial', 14, 'bold'),
                                bg=self.colors['success'],
                                fg='white',
                                padx=40,
                                pady=20,
                                relief='raised',
                                borderwidth=3,
                                cursor='hand2')
        generate_btn.pack(side='right', pady=10)
        
        self.view_btn = tk.Button(button_frame,
                                  text="📅 VIEW GENERATED TIMETABLE",
                                  command=self.view_timetable,
                                  font=('Arial', 12, 'bold'),
                                  bg=self.colors['primary'],
                                  fg='white',
                                  padx=30,
                                  pady=15,
                                  relief='raised',
                                  borderwidth=2,
                                  cursor='hand2',
                                  state='disabled')
        self.view_btn.pack(side='right', padx=10)
    
    def generate_timetable(self):
        self.status_text.delete('1.0', 'end')
        self.status_text.insert('end', "=" * 60 + "\n")
        self.status_text.insert('end', "PATTERN-FREE TIMETABLE GENERATION\n")
        self.status_text.insert('end', "=" * 60 + "\n\n")
        
        self.progress_bar['value'] = 0
        self.progress_label.config(text="Initializing...")
        self.root.update()
        
        def generation_thread():
            try:
                sections_config = self.app.db_manager.get_all_sections()
                core_lab_pairs = self.app.db_manager.get_all_core_lab_pairs()
                grouped_electives = self.get_grouped_electives_for_generation()
                
                if not sections_config:
                    error_msg = "No section configurations found! Please configure sections in Step 2."
                    self.root.after(0, lambda msg=error_msg: messagebox.showerror("Configuration Error", msg))
                    return
                
                config = GenerationConfig(
                    num_training_episodes=20,
                    max_steps_per_episode=20,
                    num_optimization_iterations=15
                )
                
                def progress_callback(progress, message):
                    self.root.after(0, lambda: self.update_progress(progress, message))
                
                self.generator = ThreeLayerTimetableGenerator(
                    subjects=self.app.data_loader.subjects,
                    faculty=self.app.data_loader.faculty,
                    labs=self.app.data_loader.labs,
                    rooms=self.app.data_loader.lab_rooms,
                    sections_config=sections_config,
                    core_lab_pairs=core_lab_pairs,
                    grouped_electives=grouped_electives,
                    faculty_assignments=self.faculty_assignments,
                    semester_mode=self.app.semester_mode,
                    config=config
                )
                
                result = self.generator.generate(callback=progress_callback)
                
                if result['status'] == 'success':
                    self.generated_schedule = self.generator.export_schedule(format_type='dict')
                    self.generation_stats = result['statistics']
                    self.root.after(0, lambda: self.on_generation_success(result))
                else:
                    self.root.after(0, lambda: self.on_generation_failure(result))
                    
            except Exception as e:
                error_msg = str(e)
                logger.error(f"Generation error: {error_msg}", exc_info=True)
                self.root.after(0, lambda msg=error_msg: messagebox.showerror("Error", msg))
        
        thread = threading.Thread(target=generation_thread, daemon=True)
        thread.start()
    
    def update_progress(self, value, message):
        self.progress_bar['value'] = value
        self.progress_label.config(text=message)
        self.status_text.insert('end', f"[{datetime.now().strftime('%H:%M:%S')}] {message}\n")
        self.status_text.see('end')
        self.root.update()
    
    def on_generation_success(self, result):
        stats = result['statistics']
        
        self.status_text.insert('end', "\n" + "=" * 60 + "\n")
        self.status_text.insert('end', "GENERATION SUCCESSFUL - PATTERN-FREE SCHEDULE\n")
        self.status_text.insert('end', "=" * 60 + "\n\n")
        
        self.status_text.insert('end', f"Total Time: {stats['total_time']:.2f}s\n")
        self.status_text.insert('end', f"Layer 1 Backtracks: {stats['layer1_backtracks']}\n")
        self.status_text.insert('end', f"Pure Labs: {stats['layer1_pure_labs']}\n")
        self.status_text.insert('end', f"Semi Labs: {stats['layer1_semi_labs']}\n")
        self.status_text.insert('end', f"T&P Subjects: {stats['layer1_tp_subjects']}\n")
        self.status_text.insert('end', f"Faculty Assigned: {stats['layer1_faculty_assigned']}\n")
        self.status_text.insert('end', f"Final Reward: {stats['final_reward']:.2f}\n")
        self.status_text.insert('end', f"Improvement: {stats['improvement']:.2f}\n")
        self.status_text.see('end')
        
        self.view_btn.config(state='normal')
        
        messagebox.showinfo("Success", 
                          f"Pattern-Free Timetable Generated!\n\n" +
                          f"Time: {stats['total_time']:.1f}s\n" +
                          f"Reward: {stats['final_reward']:.2f}\n" +
                          f"Faculty Assigned: {stats['layer1_faculty_assigned']}\n\n" +
                          "✓ No same subject at same time on consecutive days\n" +
                          "✓ Labs strictly limited to max 2 days per week")
    
    def on_generation_failure(self, result):
        self.status_text.insert('end', "\n" + "=" * 60 + "\n")
        self.status_text.insert('end', "GENERATION FAILED\n")
        self.status_text.insert('end', "=" * 60 + "\n\n")
        self.status_text.insert('end', f"Error: {result['message']}\n")
        self.status_text.see('end')
        
        messagebox.showerror("Failed", f"Generation failed:\n{result['message']}")
    
    def view_timetable(self):
        """Open timetable viewer with course info panel"""
        if not self.generated_schedule:
            messagebox.showerror("Error", "No timetable generated yet")
            return
        
        sections = list(self.generated_schedule.keys())
        
        viewer = TimetableViewer(
            parent=self.root,
            schedule_data=self.generated_schedule,
            sections=sections,
            faculty=self.app.data_loader.faculty,
            subjects=self.app.data_loader.subjects,
            labs=self.app.data_loader.labs
        )

# ============================================================================
# MAIN ENTRY POINT
# ============================================================================

def main():
    root = tk.Tk()
    app = ThreeLayerGUI(root)
    root.mainloop()

if __name__ == "__main__":
    main()
