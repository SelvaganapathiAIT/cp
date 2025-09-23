import base64
import collections
import csv
import email
import hashlib
import http.client
import imaplib
import json
import math
import os
import re
import shlex
import socket
import ssl
import string
import sys
import urllib.error
import urllib.parse
import urllib.request
from calendar import timegm
from html import escape
from datetime import date
from datetime import datetime
from datetime import time
from datetime import timedelta
from logging import getLogger
from urllib.parse import urlparse
from urllib.request import urlopen

import Crypto
import pytz
import requests
from Crypto.Cipher import AES
from dateutil.parser import parse
from dateutil.relativedelta import relativedelta
from django.contrib import messages
from django.contrib.auth.models import User
from django.core.validators import MinLengthValidator
from django.db import connection
from django.db import models
from django.db import transaction
from django.db.models import Case
from django.db.models import Count
from django.db.models import Max
from django.db.models import Q
from django.db.models import Sum
from django.db.models import When
from django.db.models.functions import Coalesce
from django.db.models.signals import post_save
from django.forms import CharField
from django.forms import EmailField
from django.forms import FileField
from django.forms import Form
from django.forms import ModelForm
from django.forms import TextInput
from django.forms import ValidationError
from django.http import HttpResponseRedirect
from django.template.loader import get_template
from django.test import RequestFactory
from django.utils import timezone
from django.utils.functional import cached_property
from googleapiclient.discovery import build
from phonenumbers import COUNTRY_CODE_TO_REGION_CODE
from pyfcm import FCMNotification
from sorl.thumbnail import ImageField
from sorl.thumbnail import get_thumbnail

import em.oauth2
import settings
from cplib.aws.s3.filenamegenerator import EfsFilenameBuilder
from cplib.cp.app_services.blacklisted_email_addresses import BlacklistedEmailAddressAppService
from cplib.email.outbound.mailgun_constants import GMAIL_ROOT_FOLDER
from cplib.email.outbound.mailgunwrapper import MailgunWrapper
from cplib.utils import constants
from cppoi.models import SicsMaster
from cppoi.points_of_interest_queries import PointsOfInterestWrapper
from em import officeservice
from map.models import LocationSearchType

logger = getLogger('django.request')


def get_email_crypt_key():
    return b'655a474dd7e2351b'


def to_ascii(s):
    return ''.join([x for x in s if x in string.printable])


def dictfetchall(cursor):
    return [dict(list(zip([col[0] for col in cursor.description], row))) for row in cursor.fetchall()]



def contact_do_import_csv_path(instance):
    """
    Creating the new path for the do import above 500 records.
    @param instance: Get the background job table object.
    @return: returns the needed file path.
    """
    return os.path.join(settings.MEDIA_ROOT,
                        'contact_do_import', str(instance.company.id),str(instance.user.id))


def get_twilio_phone_countries():
    return ['US', 'CA', ]


def get_toll_free_area_codes():
    return [888, 877, 866, 855, 800]


def cp_login_required(f):
    def wrap(request, *args, **kwargs):
        try:
            u = request.user
        except:
            u = None

        try:
            c = request.company
        except:
            c = None

        if u is None or c is None:
            messages.info(request, 'Login required')
            return HttpResponseRedirect('/login/')

        if c.disabled:
            messages.info(request, 'Account disabled')
            return HttpResponseRedirect('/login/')
        try:
            brw = request.user_profile.is_login_browser
            try:
                impors = request.old_user
            except:
                impors = False

            if brw != request.session.session_key and not impors and c.is_login_limit:
                messages.info(request,
                              'Your session has ended due to a login from another browser.')
                return HttpResponseRedirect('/logout/')

            from home.views import is_old_session_alive
            if not is_old_session_alive(request):
                return HttpResponseRedirect('/logout/')
        except:
            pass

        try:
            if request.path_info:
                menu_url = MenuURL.objects.filter(url=request.path_info)[:1][0]
                muc = MenuURLCust.objects.filter(menu_url=menu_url, company=c)[:1][0]
                if muc.hide and not (
                        request.path_info == '/users/' and
                        request.user_profile.can_view_company_directory):
                    messages.info(request, 'Permission denied')
                    return HttpResponseRedirect('/')
        except:
            pass

        return f(request, *args, **kwargs)

    wrap.__doc__ = f.__doc__
    wrap.__name__ = f.__name__
    return wrap


# Return country code for calling
def get_calling_code(iso):
    for code, isos in list(COUNTRY_CODE_TO_REGION_CODE.items()):
        if iso.upper() in isos:
            return code
    return None


def people_tab_required(f):
    def wrap(request, *args, **kwargs):
        if not request.company.people_tab:
            messages.info(request, 'Permission denied')
            return HttpResponseRedirect('/')

        return f(request, *args, **kwargs)

    wrap.__doc__ = f.__doc__
    wrap.__name__ = f.__name__
    return wrap


def cp_menu_check(arg1):
    def _method_wrapper(view_method):
        def _arguments_wrapper(request, *args, **kwargs):
            """
            Wrapper with arguments to invoke the method
            """
            try:
                murl = MenuURL.objects.filter(url=arg1)[:1][0]
                muc = MenuURLCust.objects.filter(menu_url=murl, company=request.company)[:1][0]
                if muc.hide and \
                        not (arg1 == '/users/' and request.user_profile.can_view_company_directory):
                    messages.info(request, 'Permission denied')
                    return HttpResponseRedirect('/')
            except:
                pass
            return view_method(request, *args, **kwargs)

        return _arguments_wrapper

    return _method_wrapper


def previous_weekday(d, weekday):
    previous = d.weekday() - weekday
    if previous <= 0:
        previous += 7

    return timezone.make_aware(datetime.combine(d - timedelta(days=previous), time(0, 0, 0)),
                               timezone.get_current_timezone())


# - convert datetime into unix timestamp
def unix_time(dttm=None):
    try:
        timestamp = timegm(dttm.utctimetuple())
    except:
        timestamp = ''

    return timestamp


def first_of_month(d):
    return timezone.make_aware(datetime.combine(date(d.year, d.month, 1), time(0, 0, 0)),
                               timezone.get_current_timezone())


def number_of_days(dt1, dt2):
    delta = dt1 - dt2
    return delta.days


def province_wise_states(states):
    provinces = {}
    states = states.order_by('-province', 'name')  # - for ordering US, Mexico and Canada provinces
    try:
        for state in states:
            try:
                provinces[state.province].append(state)
            except:
                provinces[state.province] = [state]
    except:
        pass
    return provinces


def get_regular_notes(post, company):
    notes = ''
    for key in post:
        if key.find('cf_') == 0:
            parts = key.split('_')
            try:
                post[key] = post[key].strip()
            except:
                pass
            try:
                id = int(parts[1])
            except:
                id = None

            cfield = CField.objects.filter(company=company, id=id).first()
            if cfield and cfield.rfield:
                n = cfield.rfield.name
                if n == 'notes':
                    notes = post[key].strip()[:4096]
    return notes


def get_parent_company(request):
    data = {}

    try:
        q = request.GET['query']
    except:
        q = ''

    data['query'] = q
    data['suggestions'] = []
    data['data'] = []

    for contact in \
            Contact.objects\
                    .filter(company=request.company,
                            title__icontains=q)\
                    .distinct('title')\
                    .order_by('title')[:20]:
        data['suggestions'].append({'value': contact.title, 'data': contact.id})
    return data


def get_autocompleted_contacts(request):
    data = {}
    q = request.GET.get('query', '')
    select_contact_opp = request.session.get('selected_opp_contact', 0)
    data['query'] = q
    data['suggestions'] = []
    data['data'] = []

    contacts = Contact.objects.filter(company=request.user_profile.company)
    contacts = contacts.filter(
        Q(first_name__icontains=q) |
        Q(last_name__icontains=q) |
        Q(contact_company__name__icontains=q)
    ).exclude(id=select_contact_opp)

    for contact in contacts:
        try:
            if request.company.people_tab:
                personnels = list(contact.contactpersonnel_set.all().values("id", "first_name", "last_name"))
                value = contact.contact_company.name
            else:
                personnels = None
                value = "{} - {} {}".format(contact.contact_company.name,
                                            contact.first_name or '',
                                            contact.last_name or '')

            data['suggestions'].append({
                'value': value,
                'data': contact.id,
                'personnels': personnels
            })
        except Exception:
            pass
    return data


def get_here_state_code(lat, lon):
    #Update here API code on 2024-05-15
    state = None
    status_code, response_data = reverse_geo_code_here_api(lat, lon)

    if status_code != 200 or not response_data or 'items' not in response_data or len(response_data['items']) == 0:
        heregeocodelog(response_data)
    else:
        here_address = response_data['items'][0]['address']
        if here_address:
            state_code = here_address.get('stateCode', '')
            province_name = here_address.get('countryName', '')
            province_name = province_name if province_name else 'United States'

            state = State.objects.filter(abbr=state_code, province=province_name).first() if state_code else None
            state = state.abbr.lower() if state else None

    return state


def get_here_address_json(lat=None, lon=None):
    address = {}

    if lat and lon:
        # Update here API code on 2024-05-15
        status_code, response_data = reverse_geo_code_here_api(lat, lon)

        if status_code != 200 or not response_data or 'items' not in response_data or len(response_data['items']) == 0:
            heregeocodelog(response_data)
        else:
            here_address = response_data['items'][0]['address']
            if here_address:
                house_number = here_address['houseNumber'].strip() if 'houseNumber' in here_address else ''
                building = here_address['building'].strip() if 'building' in here_address else ''
                street = here_address['street'].strip() if 'street' in here_address else ''
                city = here_address['city'].strip() if 'city' in here_address else ''
                state_name = here_address['state'] if 'state' in here_address else ''
                zip = here_address['postalCode'] if 'postalCode' in here_address else ''

                address = f'{house_number}{building}{street}'.strip()
                zip = zip.split('-')[0] if '-' in zip else zip

                country = Country.objects.filter(name__iexact=here_address['countryName']).first() \
                    if 'countryName' in here_address else None

                state = State.objects.filter(abbr=state_name, province=country).first() if state_name != '' else None

                address = {
                    'number': house_number,
                    'address': address,
                    'city': city,
                    'state': state,
                    'country': country,
                    'zip': zip
                }

    return address


def get_places(request, lat=None, lon=None, types=None, name=None, user_profile=None):
    n = name
    t = types

    request.session['types'] = t

    if user_profile:
        company = user_profile.company
        user = user_profile.user
    else:
        company = request.company
        user = request.user

    now = timezone.localtime(timezone.now())
    gps = None
    if lat and lon:
        radius = 100
        types = request.session.get('types', '')
        t = '&types=%s' % types if types else ''

        # get google_place_types
        if types and types.find('|') > 0:
            t_parts = types.split('|')
            if len(t_parts) > 1:
                google_place_types = []
                for tp in t_parts:
                    gpt = GooglePlaceType.objects.filter(name=tp).first()
                    if gpt:
                        google_place_types.append(gpt)
            else:
                google_place_types = GooglePlaceType.objects.filter(name=t_parts[0])
        else:
            google_place_types = GooglePlaceType.objects.filter(name=types)

        gps = GooglePlaceSearch.objects.filter(company=company,
                                               latitude=str(lat),
                                               longitude=str(lon))
        pp = re.compile('[^-a-zA-Z0-9_]')

        name = pp.sub('', name).replace('_', '+') if name else None
        if name:
            gps = gps.filter(name=name)
        else:
            gps = gps.filter(name=None)
        gps = gps.order_by('-id').first()

        if gps:
            for gpt in google_place_types:
                gps_test = GooglePlaceSearchType.objects.filter(gp_search=gps, gp_type=gpt).first()
                if gps_test is None:
                    gps = None
                    break

        if gps is None:
            n = '&name=%s' % name if name else ''
            a = get_google_places(lat, lon, radius, t, n)

            try:
                return_status = a['status']
            except:
                return_status = None

            while return_status and return_status == 'ZERO_RESULTS' and radius < 50000:
                radius *= 8
                a = get_google_places(lat, lon, radius, t, n)
                try:
                    return_status = a['status']
                except:
                    return_status = None

            if return_status and return_status == 'OK':
                gps = GooglePlaceSearch(company=company,
                                        created_by=user,
                                        latitude=str(lat)[:10],
                                        longitude=str(lon)[:11],
                                        created=now,
                                        updated=now)

                if name:
                    gps.name = name

                gps.save()

                for gpt in google_place_types:
                    gpst = GooglePlaceSearchType(gp_search=gps,
                                                 gp_type=gpt)
                    gpst.save()

                try:
                    pls = a['results']
                except:
                    pls = None

                if pls:
                    for p in pls:
                        try:
                            id = p['id']
                        except:
                            id = None

                        if id is None:
                            continue

                        try:
                            reference = p['reference']
                        except:
                            reference = None

                        if reference is None:
                            continue

                        try:
                            name = p['name'][:255]
                        except:
                            name = None

                        if name is None:
                            continue

                        try:
                            vicinity = p['vicinity']
                        except:
                            vicinity = None

                        if vicinity is None:
                            continue

                        try:
                            lat2 = str(float(p['geometry']['location']['lat']))
                        except:
                            lat2 = None

                        if lat2 is None:
                            continue

                        try:
                            lng2 = str(float(p['geometry']['location']['lng']))
                        except:
                            lng2 = None

                        if lng2 is None:
                            continue

                        distance = str(calc_distance(lat, lon, lat2, lng2))
                        if distance is None or distance == 'None':
                            distance = 0
                        address, city = None, None
                        if vicinity.find(',') > 0:
                            parts = vicinity.split(',')

                            if len(parts) == 1:
                                city = parts[0]

                            if len(parts) == 2:
                                address = parts[0]
                                city = parts[1]

                            if len(parts) == 3:
                                address = parts[0] + ' ' + parts[1]
                                city = parts[2]
                        else:
                            city = vicinity

                        address = address.strip()[:255] if address else None
                        city = city.strip() if city else None

                        country = None
                        if city and city == 'United States':
                            city = None
                            country = Country.objects.filter(name='United States').first()

                        gp = GooglePlace.objects.filter(gp_id=id).first()
                        if gp:
                            gp.gp_search = gps
                            gp.reference = reference
                            gp.name = name
                            gp.vicinity = vicinity
                            gp.address = address
                            gp.city = city
                            gp.country = country
                            gp.latitude = lat2
                            gp.longitude = lng2
                            gp.distance = distance
                            gp.updated = now
                        else:
                            gp = GooglePlace(company=company,
                                             created_by=user,
                                             gp_search=gps,
                                             gp_id=id,
                                             reference=reference,
                                             name=name,
                                             vicinity=vicinity,
                                             address=address,
                                             city=city,
                                             country=country,
                                             latitude=lat2,
                                             longitude=lng2,
                                             distance=distance,
                                             created=now,
                                             updated=now)

                        gp.save()

    places = []

    if gps:
        pls = GooglePlace.objects.filter(gp_search=gps)

        for p in pls:
            name = p.name.strip() if p.name else ''
            if len(name) == 0:
                continue

            if p.website:
                plc = p.website
            else:
                plc = ""

            abbr = p.state.abbr if p.state else ''
            place = {
                'id': p.id,
                'name': name,
                'address': p.address,
                'city': p.city,
                'state': abbr,
                'zip': p.zip or '',
                'phone_number': p.phone_number or '',
                'latitude': p.latitude,
                'longitude': p.longitude,
                'distance': p.get_distance(),
                'website': plc,
                'type': 'g'
            }

            places.append(place)

    # sorting the list
    places = sorted(places, key=lambda k: k['distance'])
    return places


def remove_special_characters(target_string):
    # Use https://www.branah.com/unicode-converter to identify the unicode values to be replaced.
    #   Do NOT specify the characters directly in this code.
    #   Come code editors will silently replace the unicode characters when you open this file,
    #   potentially replacing them with invalid values.
    return target_string.replace(u"\u2018", "'") \
        .replace(u"\u2019", "'") \
        .replace(u"\u0060", "'") \
        .replace(u"\u2032", "'")


def get_contact_details_for_export(contact, include_phones=True, include_cfields=True, **kwargs):
    """
    A common function for getting contact data for export
    :param contact: contact object
    :param include_phones: default True
    :param include_cfields: default True
    :param kwargs: required field based on include params
    :return: data list
    """

    data = [
        contact.contact_company.name,
        contact.email,
        contact.address,
        contact.address2,
        contact.city,
        contact.state.abbr if contact.state else '',
        contact.zip,
        contact.country.name if contact.country else '',
        contact.website,
        contact.created.strftime(settings.CSV_TIME_FORMAT),
        contact.last_contacted.strftime(settings.CSV_TIME_FORMAT) if contact.last_contacted else 'Never',
        contact.contact_type.name,
        contact.account,
        contact.business_type or '',
        contact.get_employee_count_range() or '',
        contact.get_annual_sales_range() or '',
        contact.county or '',
    ]

    if include_phones:
        from contacts.templatetags.contacts_extras import export_add_phone
        from contacts.templatetags.contacts_extras import export_add_phone_people_null

        home = kwargs["home"]
        office = kwargs["office"]
        cell = kwargs["cell"]
        fax = kwargs["fax"]
        hq = kwargs["hq"]
        other = kwargs["other"]

        if contact.company.people_tab:
            data = export_add_phone_people_null(data, contact, None, home,
                                                office, cell, fax, hq, other)
        else:
            data = export_add_phone(data, contact, None, home, office, cell, fax, hq, other)

    if include_cfields:
        from cfields.templatetags.cfields_extras import cfield_value_for_export
        from cfields.templatetags.cfields_extras import multi_select_value_for_export

        cfields = kwargs["cfields"]
        select = kwargs["select"]
        radio = kwargs["radio"]
        checkbox = kwargs["checkbox"]
        text = kwargs["text"]
        date_ = kwargs["date_"]
        integer = kwargs["integer"]
        auto_integer = kwargs["auto_integer"]
        decimal = kwargs["decimal"]
        time_ = kwargs["time_"]
        datetime_ = kwargs["datetime_"]
        textarea = kwargs["textarea"]
        multi_select = kwargs["multi_select"]

        for cf in cfields:
            if cf.cfield_type == multi_select:
                cf_data = multi_select_value_for_export(cf, contact)
            else:
                cf_data = cfield_value_for_export(cf, contact, select, radio, checkbox,
                                                  text, date_, integer, auto_integer,
                                                  decimal, time_, datetime_, textarea)
            if cf_data and cf_data != "None":
                data.append(str(cf_data))
            else:
                data.append('')
    return data


class PlacesCategoryList(models.Model):
    company = models.ForeignKey('Company', on_delete=models.CASCADE, null=True)
    name = models.CharField(max_length=65)


class PlacesCategory(models.Model):
    company = models.ForeignKey('Company', on_delete=models.CASCADE, null=True)
    name = models.CharField(max_length=150)
    cat_list = models.ForeignKey(PlacesCategoryList, on_delete=models.CASCADE)
    hide = models.BooleanField(default=False)
    position = models.IntegerField(default=0)

    def set_position(self, **lookup):
        try:
            pc = PlacesCategory.objects.filter(
                cat_list=self.cat_list, **lookup
            ).aggregate(max_pos=Max('position'))
        except:
            return None
        self.position = pc.get("max_pos", 0) + 1
        self.save()
        return self.position


class CategorySic(models.Model):
    category = models.ForeignKey(PlacesCategory, on_delete=models.CASCADE)
    sic = models.CharField(max_length=10)


def employee_count_dropdown():
    return [
        ("0 To 10", "0-10"),
        ("11 To 50", "11-50"),
        ("51 To 100", "51-100"),
        ("101 To 200", "101-200"),
        ("201 To 500", "201-500"),
        ("501 To 1000", "501-1000"),
        ("More Than 1000", "1000+"),
    ]


def convert_count_db_to_dropdown(value):
    try:
        cemp = int(value)
    except:
        return None

    if cemp < 11:
        result = "0-10"
    elif 10 < cemp < 51:
        result = "11-50"
    elif 50 < cemp < 101:
        result = "51-100"
    elif 100 < cemp < 201:
        result = "101-200"
    elif 200 < cemp < 501:
        result = "201-500"
    elif 500 < cemp < 1001:
        result = "501-1000"
    else:
        result = "1000+"
    return result


def convert_count_dropdown_to_db(value):
    if value == "1000+":
        return "1001"
    try:
        values = list(map(str.strip, value.split('-')))
        result = (int(values[0]) + int(values[1])) / 2
        return str(int(result))
    except:
        return None


# SIC master employee count is convert into average employee count.
def convert_employee_count_to_average_value(employee_count):
    """
    Function to convert employee count to average value
    @param employee_count: POI employee count value
    @return: Return integer of average value
    """

    try:
        # Add minimum and maximum number and return its average value
        employee_count = list(map(str.strip, employee_count.split('TO')))
        employee_count = (int(employee_count[0]) + int(employee_count[1]))/2
        if employee_count > 1001:
            # If average value greater than maximum limit
            return '1001'
        return str(int(employee_count))
    except:
        return '1001'


def annual_sales_dropdown():
    return [
        (" Less than $5 Million", "0-4"),
        ("$5 Million to $ 10 Million", "5-10"),
        ("$10 Million to $100 Million", "10-100"),
        ("More than $100 Million", "100+"),
    ]


def convert_sales_db_to_dropdown(value):
    if value == "100+":
        return value

    try:
        cemp = int(value)
    except:
        return None

    if cemp < 5000000:
        result = "0-4"
    elif 5000000 <= cemp < 10000000:
        result = "5-10"
    elif 10000000 <= cemp < 100000000:
        result = "10-100"
    else:
        result = "100+"
    return result


def convert_sales_dropdown_to_db(value):
    if value == "100+":
        return "100000001"

    try:
        values = list(map(str.strip, value.split('-')))
        result = (int(values[0]) + int(values[1])) / 2
        return str(int(result) * 1000000)
    except:
        return None


# Date : 03-02-2020
# AIT - CAL-68 : WEB - PROJECT - New Import Tool
# Desc : The below function is used to set the annual sales value based on the imported file data
def import_convert_sales_dropdown_to_db(value):
    if value == "100+":
        return "100000001"
    try:
        values = list(map(str.strip, value.split('-')))
        values[0] = int(round(float(values[0])))
        values[1] = int(round(float(values[1])))
        result = (values[0] + values[1]) / 2
        result = int(round(float(result)))
        return str(int(result) * 1000000)
    except:
        return None


def stripped(data, default=None):
    try:
        result = data.strip()
    except:
        result = default
    return result


def get_emp_count_query(employee_count, sql):
    data = convert_count_dropdown_to_db(employee_count)
    if data:
        sql = """
        %s
        AND cp_contact.employee_count = '%s'
        """ % (sql, data)
    return sql


def get_annual_sales_query(annual_sales, sql):
    data = convert_sales_dropdown_to_db(annual_sales)
    if data:
        sql = """
        %s
        AND cp_contact.annual_sales = '%s'
        """ % (sql, data)
    return sql


def filter_annual_sales_list(annual_sales_minimum_range, annual_sales_maximum_range):
    """
    Function to match annual sales value of requested filter range
    @param annual_sales_minimum_range: Filter minimum range
    @param annual_sales_maximum_range: Filter maximum range
    @return: Return list of matching annual sales range
    """

    # List of annual sales range
    annual_sales_matches = [["LESS THAN $500,000", "$500,000 TO $1 MILLION", "$1 TO 2.5 MILLION",
                            "$2.5 TO 5 MILLION"], ["$5 Million to $ 10 Million"], ["$10 TO 20 MILLION",
                            "$20 TO 50 MILLION", "$50 TO 100 MILLION"], ["$100 TO 500 MILLION",
                            "$500 MILLION TO $1 BILLION", "OVER $1 BILLION"]]
    matching_list = []
    try:
        # Return list of matching annual sales range
        for annual_sales_list in annual_sales_matches[int(annual_sales_minimum_range):int(annual_sales_maximum_range)]:
            matching_list.extend(annual_sales_list)
        return matching_list
    except:
        # Return all list of annual sales range
        for annual_sales_list in annual_sales_matches[0:]:
            matching_list.extend(annual_sales_list)
        return matching_list


def is_employee_size_in_range(average_value, employee_min_range, employee_max_range ):
    """
    Function return boolean indicates employee count is in range
    @param average_value: Average value of place employee count
    @param employee_min_range: Filter minimum range
    @param employee_max_range: Filter maximum range
    @return: Return boolean value
    """

    try:
        # Convert average, max and min value to integer
        average_value = int(average_value)
        employee_min_range = int(employee_min_range)
        employee_max_range = int(employee_max_range)
    except:
        return False
    # Check the average number in employee range and return true
    if employee_min_range <= average_value <= employee_max_range:
        return True
    return False


def get_poi_contacts(request):
    sic = request.session.get('sic')
    cat_id = request.session.get('cat_id')
    emp_count = request.session.get('emp_count', '').strip()
    ann_sales = request.session.get('ann_sales', '').strip()
    limit = request.session.get('limit')
    search = request.session.get('search')
    cmp_name = request.session.get("cmp_name")
    contact_name = request.session.get("contact_name")
    bt = request.session.get("bt")
    phone = request.session.get("phone")
    county = request.session.get("county")
    state_code = request.session.get("state_code")
    latitude = request.session.get("latitude")
    longitude = request.session.get("longitude")

    try:
        sic = int(sic)
    except:
        sic = None
    try:
        sics = CategorySic.objects.filter(category=int(cat_id)).values_list('sic', flat=True)
    except:
        sics = []
    try:
        limit = int(limit)
    except:
        limit = 0

    try:
        search = search \
            .replace('(', '\(') \
            .replace(')', '\)') \
            .replace('%', '%%') \
            .replace('?', '\?') \
            .replace("'", "''") \
            .replace('"', '') \
            .replace("$", "\$") \
            .strip()
    except:
        search = None

    sql = """
    select * from cppoi_sicsmaster
    """
    where_sql = []

    if state_code:
        state_q = []
        for i in state_code:
            state_q.append("state_code  = '{}'".format(i.upper()))
        where_sql.append("( {} )".format(' OR '.join(state_q)))

    if latitude and longitude:
        select_q = \
            "*, ((ST_DistanceSphere(st_makepoint({}, {}), geom)) / {}) as dist" \
                .format(longitude,
                        latitude,
                        settings.METER_TO_MILES)
        sql = sql.replace('*', select_q)
        pos_sql = "((ST_DistanceSphere(st_makepoint({}, {}), geom)) / {}) < 100" \
                  "".format(longitude, latitude, settings.METER_TO_MILES)
        where_sql.append(pos_sql)

    if sic:
        where_sql.append("sic_code like '{}%%'".format(sic))

    if len(sics) > 0:
        tmp = []
        for i in sics:
            tmp.append("sic_code like '{}%%'".format(i))
        where_sql.append('( {} )'.format(' OR '.join(tmp)))

    if emp_count:
        where_sql.append("UPPER(employee_count) = '{}'".format(emp_count))

    if ann_sales:
        where_sql.append("UPPER(annual_sales) = '{}'".format(ann_sales))

    if search:
        search_q = []
        if cmp_name:
            search_q.append("company_name ILIKE '%%{}%%'".format(search))

        if contact_name:
            search_q.append("contact_name ILIKE '%%{}%%'".format(search))

        if bt:
            search_q.append("business_type ILIKE '%%{}%%'".format(search))

        if phone:
            search_q.append("phone_number = '{}'".format(search.replace('-', '')))

        if county:
            search_q.append("county ILIKE '%%{}%%'".format(search))

        if search_q:
            where_sql.append("( {} )".format(' OR '.join(search_q)))

    if len(where_sql) != 0:
        sql += 'where ' + ' AND '.join(where_sql)

    if latitude and longitude:
        sql += " ORDER BY dist"

    if limit != 0:
        sql += " LIMIT {} ".format(limit)
    objs = SicsMaster.objects.raw(sql).using('cppoi')
    return list(objs)


def get_pois(request, state_code, lat=None, lon=None, cat='', query=None, page=1, limit_radius=25,
             max_result="10", zip_code=None):
    # WARN: This is used by both the mobile and web apps. Be very careful about making
    #   changes that would alter the identifiers that are returned.
    #   This function is currently called from 5 other functions.

    # If a category is selected, pass then retrieve the sic code list
    sic_id_list = []
    if cat != '' and cat.isdigit():
        sic_id_list = CategorySic.objects.filter(category=cat).values_list('sic', flat=True)

    # Retrieve a list of points of interest that are available from the POI database
    points_of_interest = PointsOfInterestWrapper.get_points_of_interest(state_code,
                                                                        lat,
                                                                        lon,
                                                                        sic_id_list,
                                                                        query,
                                                                        page,
                                                                        limit_radius,
                                                                        max_result,
                                                                        zip_code)

    # Cache the current datetime, which will be used if we need to create database entries
    now = timezone.localtime(timezone.now())

    # If a corresponding record doesn't exist in the GooglePlaceSearch table, create one
    try:
        google_place_search = GooglePlaceSearch.objects.filter(company=request.company,
                                                               latitude=str(lat),
                                                               longitude=str(lon))[:1][0]
    except:
        google_place_search = GooglePlaceSearch(company=request.company,
                                                created_by=request.user,
                                                latitude=str(lat),
                                                longitude=str(lon),
                                                created=now,
                                                updated=now)
        google_place_search.save()

    places = []
    country = Country.objects.filter(name='United States')[:1][0]
    province_name = get_user_country_name(request.user.userprofile)
    states_list = list(State.objects.filter(province=province_name).order_by("name"))

    # Iterate over the points of interest and attempt to identify the GooglePlace they
    #   are associated with.
    for point_of_interest in points_of_interest:
        gp_id = point_of_interest.geom.strip()
        name = point_of_interest.company_name.strip()
        vicinity = point_of_interest.address.strip()
        address = vicinity
        city = stripped(point_of_interest.city)
        lat2 = point_of_interest.latitude
        lng2 = point_of_interest.longitude
        business_type = stripped(point_of_interest.business_type)
        employee_count = stripped(point_of_interest.employee_count)
        annual_sales = stripped(point_of_interest.annual_sales)
        county = stripped(point_of_interest.county)
        contact_name = stripped(point_of_interest.contact_name)
        title = stripped(point_of_interest.title)
        
        # Match the state_code from this POI entry to the list of states
        state = None
        for state_entry in states_list:
            if state_entry.abbr.strip().upper() == point_of_interest.state_code.strip().upper():
                state = state_entry
                break

        try:
            distance = point_of_interest.dist
        except:
            distance = 0

        if distance is None or distance == 'None':
            distance = 0

        formatted_zip_code = stripped(point_of_interest.zip_code)
        phone_number = point_of_interest.phone_number
        website = point_of_interest.website

        # Get or Create a record in GooglePlace table.
        # NOTE: This loop iterates over the POI data up to 30 times, which causes the POI
        #   database to be exceptionally slow for most users. We need to do something
        #   about this because the actual search in the POI database is actually quite fast.
        #   The part that's really slow is this loop, which tests to see if each
        #   GooglePlace is present in the database and if it isn't, creates it.
        try:
            google_place = GooglePlace.objects.filter(company=request.company,
                                                      gp_id=gp_id,
                                                      name=name,
                                                      address=address)[:1][0]
        except:
            google_place = GooglePlace(company=request.company,
                                       created_by=request.user,
                                       gp_id=gp_id,
                                       gp_search=google_place_search,
                                       name=name,
                                       vicinity=vicinity,
                                       address=address,
                                       city=city,
                                       zip=formatted_zip_code,
                                       state=state,
                                       phone_number=phone_number,
                                       website=website,
                                       country=country,
                                       latitude=lat2,
                                       longitude=lng2,
                                       distance=distance,
                                       business_type=business_type,
                                       employee_count=employee_count,
                                       annual_sales=annual_sales,
                                       county=county,
                                       contact_name=contact_name,
                                       title=title,
                                       created=now,
                                       updated=now)
            google_place.save()

        name = google_place.name.strip() if google_place.name else ''
        if len(name) == 0:
            continue

        abbr = google_place.state.abbr if google_place.state else ''
        website = google_place.website

        # If a website is listed, but doesn't start with a valid prefix, add a default prefix
        if website and not (website.startswith("http://") or website.startswith("https://")):
            website = "http://" + website

        # WARN: The lookup for the record_color creates a recursive lookup that's never
        #   going to have good performance. I'm not sure how we can do this without breaking
        #   the existing functionality.
        record_color = google_place.record_color(request.user)

        # Format the data into a dictionary object and append it to the list of places
        #   that will be returned.
        place = {
            'id': google_place.id,
            'name': google_place.name,
            'address': google_place.address,
            'city': google_place.city,
            'state': abbr,
            'zip': google_place.zip or '',
            'phone_number': google_place.phone_number or '',
            'latitude': google_place.latitude,
            'longitude': google_place.longitude,
            'distance': str(round(distance, 2)) + ' M',
            'record_color': record_color,
            'website': website,
            'type': 'g'
        }

        # Appended to the places list
        places.append(place)

    return places


def get_advance_pois_search_filters(request, state_code, lat=None, lon=None, category_list=[], query=None,
                                    limit_radius=25, max_result=20, zip_code=None, employee_minimum_range=0,
                                    employee_maximum_range=1001, annual_sales_minimum_range=0,
                                    annual_sales_maximum_range=3):
    # NOTE: This function is only used by web apps places filters.
    #   This function is currently called from 1 function from map.

    # If a category is selected, pass then retrieve the sic code list
    sic_ids_list = []

    # Check the category is selected and filter its category sic code list
    if category_list:
        # Check and get category sic list for selected category
        for category in category_list:
            category_sic_id_list = CategorySic.objects.filter(category=category).values_list('sic', flat=True)
            if category_sic_id_list:
                sic_ids_list.extend(category_sic_id_list)
    # Indicates search request from web page
    web_search = True
    page = 1

    # Retrieve a list of points of interest that are available from the POI database
    points_of_interest = PointsOfInterestWrapper.get_points_of_interest(state_code,
                                                                        lat,
                                                                        lon,
                                                                        sic_ids_list,
                                                                        query,
                                                                        page,
                                                                        limit_radius,
                                                                        max_result,
                                                                        zip_code,
                                                                        web_search)
    # Cache the current datetime, which will be used if we need to create database entries
    now = timezone.localtime(timezone.now())

    # Check the annual_sales between selected range
    matching_annual_sales_range_list = filter_annual_sales_list(annual_sales_minimum_range, annual_sales_maximum_range)

    # If a corresponding record doesn't exist in the GooglePlaceSearch table, create one
    try:
        google_place_search = GooglePlaceSearch.objects.filter(company=request.company,
                                                               latitude=str(lat),
                                                               longitude=str(lon))[:1][0]
    except:
        google_place_search = GooglePlaceSearch(company=request.company,
                                                created_by=request.user,
                                                latitude=str(lat),
                                                longitude=str(lon),
                                                created=now,
                                                updated=now)
        google_place_search.save()

    places = []
    country = Country.objects.filter(name='United States')[:1][0]
    province_name = get_user_country_name(request.user.userprofile)
    states_list = list(State.objects.filter(province=province_name).order_by("name"))

    # Iterate over the points of interest and attempt to identify the GooglePlace they
    #   are associated with.
    for point_of_interest in points_of_interest:
        gp_id = point_of_interest.geom.strip()
        name = point_of_interest.company_name.strip()
        vicinity = point_of_interest.address.strip()
        address = vicinity
        city = stripped(point_of_interest.city)
        lat2 = point_of_interest.latitude
        lng2 = point_of_interest.longitude
        business_type = stripped(point_of_interest.business_type)
        employee_count = convert_employee_count_to_average_value(point_of_interest.employee_count)
        annual_sales = stripped(point_of_interest.annual_sales)
        county = stripped(point_of_interest.county)
        contact_name = stripped(point_of_interest.contact_name)
        title = stripped(point_of_interest.title)

        # Check the employee count between selected range
        is_valid_employee_count = is_employee_size_in_range(employee_count,
                                                            employee_minimum_range,
                                                            employee_maximum_range)

        # Check the employee count and annual sales and maximum result
        if is_valid_employee_count and\
                annual_sales in matching_annual_sales_range_list and\
                len(places) <= int(max_result):
            # Match the state_code from this POI entry to the list of states
            state = None
            for state_entry in states_list:
                if state_entry.abbr.strip().upper() == point_of_interest.state_code.strip().upper():
                    state = state_entry
                    break

            try:
                distance = point_of_interest.dist
            except:
                distance = 0

            if distance is None or distance == 'None':
                distance = 0

            formatted_zip_code = stripped(point_of_interest.zip_code)
            phone_number = point_of_interest.phone_number
            website = point_of_interest.website

            # Get or Create a record in GooglePlace table.
            # NOTE: This loop iterates over the POI data up to 30 times, which causes the POI
            #   database to be exceptionally slow for most users. We need to do something
            #   about this because the actual search in the POI database is actually quite fast.
            #   The part that's really slow is this loop, which tests to see if each
            #   GooglePlace is present in the database and if it isn't, creates it.
            try:
                google_place = GooglePlace.objects.filter(company=request.company,
                                                          gp_id=gp_id,
                                                          name=name,
                                                          address=address)[:1][0]
            except:
                google_place = GooglePlace(company=request.company,
                                           created_by=request.user,
                                           gp_id=gp_id,
                                           gp_search=google_place_search,
                                           name=name,
                                           vicinity=vicinity,
                                           address=address,
                                           city=city,
                                           zip=formatted_zip_code,
                                           state=state,
                                           phone_number=phone_number,
                                           website=website,
                                           country=country,
                                           latitude=lat2,
                                           longitude=lng2,
                                           distance=distance,
                                           business_type=business_type,
                                           employee_count=stripped(point_of_interest.employee_count),
                                           annual_sales=annual_sales,
                                           county=county,
                                           contact_name=contact_name,
                                           title=title,
                                           created=now,
                                           updated=now)
                google_place.save()

            name = google_place.name.strip() if google_place.name else ''
            if len(name) == 0:
                continue

            abbr = google_place.state.abbr if google_place.state else ''
            website = google_place.website

            # If a website is listed, but doesn't start with a valid prefix, add a default prefix
            if website and not (website.startswith("http://") or website.startswith("https://")):
                website = "http://" + website

            # WARN: The lookup for the record_color creates a recursive lookup that's never
            #   going to have good performance. I'm not sure how we can do this without breaking
            #   the existing functionality.
            record_color = google_place.record_color(request.user)

            # Format the data into a dictionary object and append it to the list of places
            #   that will be returned.
            place = {
                'id': google_place.id,
                'name': google_place.name,
                'address': google_place.address,
                'city': google_place.city,
                'state': abbr,
                'zip': google_place.zip or '',
                'phone_number': google_place.phone_number or '',
                'latitude': google_place.latitude,
                'longitude': google_place.longitude,
                'distance': str(round(distance, 2)) + ' M',
                'record_color': record_color,
                'website': website,
                'type': 'g'
            }
            # Appended to the places list
            places.append(place)

    # Return the max result places
    return places[:int(max_result)]


def geocode_here_address(address=''):
    if address is None or address == 'None' or address == '' or address == 0:
        return [None, None, None]

    address = address.strip()
    address = re.sub(r'[^a-zA-Z0-9]', '+', address)

    latitude, longitude, state_code = None, None, ''

    status_code, response_data = geo_code_search_api(address)

    if status_code != 200 or not response_data or 'items' not in response_data or len(response_data['items']) == 0:
        heregeocodelog(response_data)
    else:
        here_geocode = response_data['items'][0]['address']
        position_data = response_data['items'][0]

        latitude = str(position_data.get('position', {}).get('lat', ''))
        longitude = str(position_data.get('position', {}).get('lng', ''))
        
        state_name = here_geocode.get('state', '')
        state_code = here_geocode.get('stateCode', '')

        state = State.objects.filter(name=state_name, abbr=state_code).first() if state_name != '' else None
        state_code = state.abbr.lower() if state else ''

    return [latitude, longitude, state_code]


def clear_page_number(request):
    k = '%s_page' % request.module_view_name
    try:
        del request.session[k]
    except:
        pass


def get_page_number(request):
    k = '%s_page' % request.module_view_name
    try:
        page = int(request.GET['page'])
    except:
        page = None
    if page is None:
        try:
            page = request.session[k]
        except:
            page = None
    if page is None:
        page = 1
    request.session[k] = page
    return page


def send_eform_emails(request, cef=None, resend=False, contact_company_name=None):
    txt_template = get_template('mail/_eventform.txt')
    html_template = get_template('mail/_eventform.html')
    eformlog("%s----Called" % cef.id, request.company)

    context = {'media_url': settings.MEDIA_URL,
               'url': settings.APP_URL,
               'email_user': request.user_profile,
               'year': timezone.localtime(timezone.now()).year,
               'today': timezone.localtime(timezone.now()).strftime('%Y-%m-%d'),
               'cef': cef}
    eformlog("%s----Template created" % cef.id, request.company)
    body_text = txt_template.render(context, request)
    body_html = html_template.render(context, request)

    # Get the black listed email address list
    blacklisted_email_addresses_list = BlacklistedEmailAddressAppService.\
        get_blacklisted_emailaddresses_list()
    for efe in EventFormEMail.objects.filter(event_form=cef.event_form):
        if efe.email in blacklisted_email_addresses_list:
            # Skip if the email address is in the blacklist
            continue
        eformlog("%s----Event form mail id %s" % (cef.id, efe.event_form_id), request.company)
        event_form = EventForm.objects.filter(id=efe.event_form_id).first()
        if event_form:
            subject = 'Event Form - %s ' % event_form.name

            if contact_company_name:
                subject = '%s - %s' % (subject, contact_company_name)
        else:
            subject = 'CallProof Event Form'

        if resend:
            subject = '[UPDATED] %s' % subject

        # Get the MailgunWrapper class
        mailgun_wrapper = MailgunWrapper([efe.email],
                                         subject,
                                         body_text,
                                         body_html,
                                         {'References': settings.FROM_EMAIL})
        # Send the email
        try:
            mailgun_wrapper.send_email()
            eformlog("%s----MSG sent %s" % (cef.id, efe.event_form_id), request.company)
        except Exception as e:
            eformlog("%s----Exception occur %s %s" % (cef.id, efe.event_form_id, e),
                     request.company)
            pass

    if cef.event_form.send_email_to_rep:
        if cef.event_form:
            subject = 'Event Form - %s ' % cef.event_form.name

            if contact_company_name:
                subject = '%s - %s' % (subject, contact_company_name)
        else:
            subject = 'CallProof Event Form'

        if resend:
            subject = '[UPDATED] %s' % subject

        # Get the MailgunWrapper class
        mailgun_wrapper = MailgunWrapper([request.user.email],
                                         subject,
                                         body_text,
                                         body_html)
        # Send the email
        try:
            mailgun_wrapper.send_email()
        except Exception as e:
            eformlog("%s----Exception occur1 %s" % (cef.id, e), request.company)
            pass


def do_eform_post_back(request, cef=None):
    ef = cef.event_form

    if ef.post_back_url:
        try:
            o = urlparse(ef.post_back_url)
        except:
            o = None

        if o:
            try:
                scheme = o.scheme
            except:
                scheme = None

            try:
                netloc = o.netloc
            except:
                netloc = None

            try:
                path = o.path
            except:
                path = None

            h = None

            if scheme:
                if scheme == 'http':
                    h = http.client.HTTPConnection(netloc)
                elif scheme == 'https':
                    h = http.client.HTTPSConnection(netloc)

            if h and netloc and path:
                params = {}
                if ef.post_back_secret:
                    params['secret_key'] = ef.post_back_secret

                from cfields.templatetags.cfields_extras import get_cfield_value

                for cf in cef.get_cfields():
                    params[cf.name.replace(' ', '_').lower()] = get_cfield_value(cf, cef)

                params = urllib.parse.urlencode(params)

                if ef.post_back_method == 0:
                    h.request('GET', path, params)
                elif ef.post_back_method == 1:
                    headers = {
                        'Content-type': 'application/x-www-form-urlencoded',
                        'Accept': 'text/plain'
                    }
                    h.request('POST', path, params, headers)

                try:
                    r = h.getresponse()
                except:
                    r = None

                if r:
                    try:
                        status = int(r.status)
                    except:
                        status = 400

                    try:
                        reason = r.reason[:64]
                    except:
                        reason = 'Bad Request'

                    try:
                        response = r.read().strip()[:4096]
                    except:
                        response = ''

                    try:
                        url = o.geturl()[:255]
                    except:
                        url = ''

                now = timezone.localtime(timezone.now())
                pbl = EventFormPostBackLog(company=request.company,
                                           event_form=ef,
                                           url=url,
                                           method=ef.post_back_method,
                                           request=params,
                                           status=status,
                                           reason=reason,
                                           response=response,
                                           created=now)
                pbl.save()


def name_suffixes():
    return ['ii', 'iii', 'jr', 'sr', 'jr.', 'sr.']


def eformlog(log, company=None):
    try:
        if company and company.id in [4966, 6177, 9665]:
            with open('%s/eformlog.log' % settings.LOGS, 'a') as f:
                f.write('%s\n' % log)
    except:
        pass


def maillog(log):
    if settings.DO_LOGGING:
        with open('%s/maillog.log' % settings.LOGS, 'a') as f:
            f.write('%s\n' % log)


def heregeocodelog(log):
    # if settings.DO_LOGGING:
    with open('%s/heregeocodelog.log' % settings.LOGS, 'a') as f:
        f.write('%s\n' % log)


def call_debug(log):
    try:
        with open('%s/call_debug_log.log' % settings.LOGS, 'a') as f:
            f.write('[%s] %s\n' % (timezone.localtime(timezone.now()), log))
    except:
        pass


def app_fcm_log(log):
    with open('%s/appfcm.log' % settings.LOGS, 'a', encoding='utf-8') as f:
        f.write('%s\n' % log)


def office365_login_issue(step, log):
    with open('%s/office365.log' % settings.LOGS, 'a') as f:
        f.write('%s\n' % step)
        f.write('%s\n' % log)


def incomingcalllog(log):
    # if settings.DO_LOGGING:
    with open('%s/incomingcalllog.log' % settings.LOGS, 'a') as f:
        f.write('%s\n' % log)


def auth_net_log(log):
    if settings.DO_LOGGING:
        with open('%s/authnet.log' % settings.LOGS, 'a') as f:
            f.write('%s\n\n' % log)


def login_log(log):
    if settings.DO_LOGGING:
        with open('%s/login.log' % settings.LOGS, 'a') as f:
            f.write('%s\n\n' % log)


def m_login_log(log):
    if settings.DO_LOGGING:
        with open('%s/m_login.log' % settings.LOGS, 'a') as f:
            f.write('%s\n\n' % log)


def twilio_log(log):
    if True:
        with open('%s/twilio.log' % settings.LOGS, 'a', encoding='utf-8') as f:
            f.write('{}: {}\n\n'.format(str(datetime.utcnow()), log))


def hustle_api_log(log):
    if False:
        with open('%s/hustle_api.log' % settings.LOGS, 'a') as f:
            f.write('%s\n\n' % log)


def duplicate_contacts_log(log):
    if True:
        with open('%s/duplicate_contacts.log' % settings.LOGS, 'a', encoding='utf-8') as f:
                f.write('%s\n\n' % log)


def glass_america_dashboard_log(log):
    # GlassAmerica Dashboard monitor
    with open('%s/glass_america_dashboard.log' % settings.LOGS, 'a', encoding='utf-8') as f:
        f.write('%s\n\n' % log)


def do_import_account_log(log):
    # Do import tool monitor
    with open('%s/do_import_account.log' % settings.LOGS, 'a', encoding='utf-8') as f:
        f.write('{}: {}\n\n'.format(str(datetime.utcnow()), log))


def get_place_cats():
    return [
        'accounting',
        'airport',
        'amusement_park',
        'aquarium',
        'art_gallery',
        'atm',
        'bakery',
        'bank',
        'bar',
        'beauty_salon',
        'bicycle_store',
        'book_store',
        'bowling_alley',
        'bus_station',
        'cafe',
        'campground',
        'car_dealer',
        'car_rental',
        'car_repair',
        'car_wash',
        'casino',
        'cemetery',
        'church',
        'city_hall',
        'clothing_store',
        'convenience_store',
        'courthouse',
        'dentist',
        'department_store',
        'doctor',
        'electrician',
        'electronics_store',
        'embassy',
        'establishment',
        'finance',
        'fire_station',
        'florist',
        'food',
        'funeral_home',
        'furniture_store',
        'gas_station',
        'general_contractor',
        'geocode',
        'grocery_or_supermarket',
        'gym',
        'hair_care',
        'hardware_store',
        'health',
        'hindu_temple',
        'home_goods_store',
        'hospital',
        'insurance_agency',
        'jewelry_store',
        'laundry',
        'lawyer',
        'library',
        'liquor_store',
        'local_government_office',
        'locksmith',
        'lodging',
        'meal_delivery',
        'meal_takeaway',
        'mosque',
        'movie_rental',
        'movie_theater',
        'moving_company',
        'museum',
        'night_club',
        'painter',
        'park',
        'parking',
        'pet_store',
        'pharmacy',
        'physiotherapist',
        'place_of_worship',
        'plumber',
        'police',
        'post_office',
        'real_estate_agency',
        'restaurant',
        'roofing_contractor',
        'rv_park',
        'school',
        'shoe_store',
        'shopping_mall',
        'spa',
        'stadium',
        'storage',
        'store',
        'subway_station',
        'synagogue',
        'taxi_stand',
        'train_station',
        'travel_agency',
        'university',
        'veterinary_care',
        'zoo',
        'administrative_area_level_1',
        'administrative_area_level_2',
        'administrative_area_level_3',
        'colloquial_area',
        'country',
        'floor',
        'intersection',
        'locality',
        'natural_feature',
        'neighborhood',
        'political',
        'point_of_interest',
        'post_box',
        'postal_code',
        'postal_code_prefix',
        'postal_town',
        'premise',
        'room',
        'route',
        'street_address',
        'street_number',
        'sublocality',
        'sublocality_level_4',
        'sublocality_level_5',
        'sublocality_level_3',
        'sublocality_level_2',
        'sublocality_level_1',
        'subpremise',
        'transit_station'
    ]


def get_billing_date():
    today = timezone.localtime(timezone.now()).date()
    # skip 29, 30, 31
    day = 1 if today.day > 28 else today.day
    # increase month if skipping days
    month = today.month + 1 if today.day > 28 else today.month
    # adjust year if month is 13
    year = today.year if month < 13 else today.year + 1
    # fix month
    month = 1 if month == 13 else month

    return timezone.make_aware(datetime.combine(date(year, month, day), time(0, 0, 0)),
                               timezone.get_current_timezone()).date()


def get_twilio_call_results():
    return ['Left Voice Mail',
            'Left Message With Operator',
            'Followup Request',
            'Set Appointment',
            'Proposal Requested',
            'Not A Prospect',
            'Closed Deal',
            'Wrong Number',
            'Not Interested']


def get_campaign_keys():
    return ['manager_daily_report',
            'employee_daily_report',
            'manager_summary_report',
            'manager_scheduled_report',
            'employee_followup_reminder',
            'employee_incoming_sms',
            'appointment_report',
            'default_assign_sales_rep',
            'google_transcription',
            'prefill_opportunity_custom_field']


# Date : 16-06-2020
# AIT - CPV1-110 : WEB - PROJECT - Add the Manager Production Report as a Daily Option
# Desc : Below changes used to add manager production daily report option
def get_setting_keys():
    return ['manager_daily_report',
            'manager_summary_report',
            'manager_production_report_daily',
            'manager_production_report_week',
            'manager_production_report_month',
            'employee_daily_report',
            'employee_followup_reminder',
            'employee_unsubscribe',
            'appointment_report']


def ident_phone(call=None, phone_number=None):
    now = timezone.localtime(timezone.now())
    # The Contact id is sent from the mobile apps so match it back to the exact contact
    # they have contacted.
    # If call made to reps we get the contact id as 0 and we save it as None
    # in cp_call table under contact_id column
    try:
        contact_id = call.contact_id
    except:
        contact_id = None

    user = call.user
    if user is None:
        return False

    try:
        user_profile = user.userprofile
    except:
        user_profile = None

    if user_profile is None:
        return False

    company = user_profile.company
    if company is None:
        return False

    if phone_number is None:
        pn = call.phone_number
    else:
        pn = phone_number

    call_type = call.call_type
    if call_type is None:
        return False

    if contact_id:
        # AIT - 30-03-2020
        # In Glass America new account when no record found for phone number for the
        # contact id the call_ident script is not executed.
        try:
            contact_phone = ContactPhone.objects.filter(contact_id=contact_id)[:1]
            contact_phone = contact_phone[0].id
            co = CallOverride.objects.filter(company=company,
                                             phone_number=pn,
                                             contact_phone_id=contact_phone)[:1]
        except:
            co = None
    else:
        co = CallOverride.objects.filter(company=company, phone_number=pn)[:1]

    try:
        co = co[0]
    except:
        co = None

    if co:
        contact_phone = co.contact_phone
        call.contact_phone = contact_phone
        call.save()
        call.add_followup_call()
        contact = contact_phone.contact
        if contact.last_contacted is None or contact.last_contacted < call.start:
            contact.last_contacted = call.start
        contact.updated = now
        contact.save()
        name = 'contact_call_%s' % call_type.name
        user_profile.add_event(name=name,
                               contact=contact_phone.contact,
                               call=call,
                               start=call.start,
                               duration=call.duration,
                               created=call.start)
        user_profile.add_contact_rep(contact)
        return True

    if contact_id:
        contact_phone = ContactPhone.objects.filter(company=company,
                                                    contact_id=contact_id,
                                                    phone_number=pn,
                                                    unknown=False)[:1]
    else:
        contact_phone = ContactPhone.objects.filter(company=company,
                                                    phone_number=pn,
                                                    unknown=False)[:1]
    try:
        contact_phone = contact_phone[0]
    except:
        if len(pn) > 9:
            try:
                if contact_id:
                    contact_phone = ContactPhone.objects.filter(company=company,
                                                                contact_id=contact_id,
                                                                phone_number__icontains=pn,
                                                                unknown=False)[:1]
                else:
                    contact_phone = ContactPhone.objects.filter(company=company,
                                                                phone_number__icontains=pn,
                                                                unknown=False)[:1]
                contact_phone = contact_phone[0]
            except:
                contact_phone = None

    if contact_phone:
        call.contact_phone = contact_phone
        call.save()
        call.add_followup_call()
        contact = contact_phone.contact
        if contact.last_contacted is None or contact.last_contacted < call.start:
            contact.last_contacted = call.start
        contact.updated = now
        contact.save()
        name = 'contact_call_%s' % call_type.name
        user_profile.add_event(name=name,
                               contact=contact_phone.contact,
                               call=call,
                               start=call.start,
                               duration=call.duration,
                               created=call.start)
        user_profile.add_contact_rep(contact)
        return True

    user_phone = UserPhone.objects.filter(company=company, phone_number=pn).first()
    # skip calls to self (voicemail)
    if user_phone and call.user_id != user_phone.user_id:
        call.user_phone = user_phone
        call.save()
        up = call.user.userprofile
        if up is not None:
            name = 'employee_call_%s' % call_type.name
            up.add_event(name=name,
                         other_user=user_phone.user,
                         call=call,
                         start=call.start,
                         duration=call.duration,
                         created=call.start)
        return True

    google_place = GooglePlace.objects.filter(company=company, phone_number=pn).first()
    if google_place:
        call.google_place = google_place
        call.save()
        up = call.user.userprofile
        if up is not None:
            name = 'place_call_%s' % call_type.name
            up.add_event(name=name,
                         google_place=google_place,
                         call=call,
                         start=call.start,
                         duration=call.duration,
                         created=call.start)
        return True
    return False


def ident_twilio_incoming(twilio_call=None, phone_number=None):
    now = timezone.localtime(timezone.now())
    pn = phone_number

    if pn is None:
        pn = twilio_call.caller

    call_type = twilio_call.call_type
    if call_type is None:
        return False

    try:
        up = twilio_call.user.userprofile
    except:
        up = None

    company = twilio_call.company

    co = CallOverride.objects.filter(company=company, phone_number=pn).first()
    if co:
        contact_phone = co.contact_phone
        twilio_call.contact_phone = contact_phone
        twilio_call.save()
        contact = contact_phone.contact
        if contact.last_contacted is None or contact.last_contacted < twilio_call.start:
            contact.last_contacted = twilio_call.start
        contact.updated = now
        contact.save()

        if up:
            name = 'contact_call_%s' % call_type.name
            up.add_event(name=name,
                         contact=contact_phone.contact,
                         tc=twilio_call,
                         start=twilio_call.start,
                         duration=twilio_call.duration,
                         created=twilio_call.start)
            up.add_contact_rep(contact)
        return True

    contact_phone = ContactPhone.objects.filter(company=company, phone_number=pn).first()
    if contact_phone:
        twilio_call.contact_phone = contact_phone
        twilio_call.save()
        contact = contact_phone.contact
        if contact.last_contacted is None or contact.last_contacted < twilio_call.start:
            contact.last_contacted = twilio_call.start
        contact.updated = now
        contact.save()
        if up:
            name = 'contact_call_%s' % call_type.name
            up.add_event(name=name,
                         contact=contact_phone.contact,
                         tc=twilio_call,
                         start=twilio_call.start,
                         duration=twilio_call.duration,
                         created=twilio_call.start)
            up.add_contact_rep(contact)
        return True

    user_phone = UserPhone.objects.filter(company=company, phone_number=pn).first()
    # skip calls to self (voicemail)
    if user_phone and twilio_call.user_id != user_phone.user_id:
        twilio_call.user_phone = user_phone
        twilio_call.save()

        if up:
            name = 'employee_call_%s' % call_type.name
            up.add_event(name=name,
                         other_user=user_phone.user,
                         tc=twilio_call,
                         start=twilio_call.start,
                         duration=twilio_call.duration,
                         created=twilio_call.start)
        return True

    google_place = GooglePlace.objects.filter(company=company, phone_number=pn).first()
    if google_place:
        twilio_call.google_place = google_place
        twilio_call.save()
        up = twilio_call.user.userprofile
        if up is not None:
            name = 'place_call_%s' % call_type.name
            up.add_event(name=name,
                         google_place=google_place,
                         tc=twilio_call,
                         start=twilio_call.start,
                         duration=twilio_call.duration,
                         created=twilio_call.start)
        return True

    return False


# To sends the email notification
def send_notify_new_member_email(user_profile=None, company=None, application_name=None,
                                 ip_info_dict=None, source='website', device_type=None):
    company = Company.objects.filter(id=company.id).first()
    if company is None:
        return

    now = timezone.localtime(timezone.now())

    try:
        referer_url = company.referer_url.name
    except:
        referer_url = ''

    if application_name:
        app_name = application_name
    else:
        app_name = "CallProof"

    platform = "CallProof Classic"

    body_text = """

Someone signed up for %s!

Name: %s

Company: %s

Email: %s

When: %s

Phone: %s

Referer URL: %s

Referer Info:
""" % (app_name,
       user_profile.fullname(),
       company.name,
       user_profile.email(),
       timezone.localtime(timezone.now()).strftime('%Y/%m/%d %I:%M%p'),
       user_profile.signup_phone(),
       referer_url)

    for v in company.referer_vars():
        body_text += """

%s: %s

""" % (v.name_pretty(), v.content_pretty())

    body_text += """

Recent Signups: %s/admin/cp/userprofile/?manager__exact=1

"""% settings.APP_URL

    # setting IP Address related Info
    if ip_info_dict:
        body_text += """

IP address information for %s!

IP Address: %s

Country: %s

City: %s

location: %s

timezone: %s

platform: %s

Device: %s

""" % (user_profile.fullname(),
       ip_info_dict['ip_add'],
       ip_info_dict['country_name'],
       ip_info_dict['city'],
       ip_info_dict['location'],
       ip_info_dict['timezone'],
       platform,
       device_type)

    # Get the MailgunWrapper class
    mailgun_wrapper = MailgunWrapper(settings.SIGNUP_RECIPIENTS,
                                     'CallProof Signup',
                                     body_text,
                                     body_text.replace('\n', '<br />'))
    # Send the email
    mailgun_wrapper.send_email()

    for acc_id in settings.DEFAULT_SIGNUP_CONTACT_ACCOUNT:
        # put contact into Callproof LLC's contacts
        absolute = Company.objects.filter(id=acc_id).first()
        if absolute:
            created_by = absolute.get_first_manager()
            # WARN: The acc_pos is used to reference the index of a value in another array.
            #   This is dangerous, error prone and there's no good reason for it to work this way.
            acc_pos = settings.DEFAULT_SIGNUP_CONTACT_ACCOUNT.index(acc_id)
            if source == 'website':
                # WARN: This should be updated because it uses the index of one array to reference
                #   the index of another array, both of which are defined elsewhere and aren't
                #   obviously related to one another in a way that makes it easy to see there
                #   would be a problem if you changed it.
                option_id = settings.DEFAULT_SIGNUP_CONTACT_ACCOUNT_LEAD_SCOURCE_OPTION_WEB[acc_pos]
                prev_contact = 'Website Signup'
                signups = ContactType.objects.filter(company=absolute,
                                                     id=settings.DEFAULT_SIGNUP_CONTACT_ACCOUNT_CONTACTTYPE_WEB[
                                                         acc_pos])[:1]
            elif source == 'mobile':
                # WARN: This should be updated because it uses the index of one array to reference
                #   the index of another array, both of which are defined elsewhere and aren't
                #   obviously related to one another in a way that makes it easy to see there
                #   would be a problem if you changed it.
                option_id = settings.DEFAULT_SIGNUP_CONTACT_ACCOUNT_LEAD_SCOURCE_OPTION_APP[acc_pos]
                prev_contact = 'App Signup'
                signups = ContactType.objects.filter(company=absolute,
                                                     id=settings.DEFAULT_SIGNUP_CONTACT_ACCOUNT_CONTACTTYPE_MOB[
                                                         acc_pos])[:1]
            try:
                signups = signups[0]
            except:
                signups = None
            if signups:
                cc = None
                new_cc_id = None
                if cc is None:
                    cc = ContactCompany(company=absolute,
                                        name=company.name,
                                        created=now,
                                        updated=now)
                    cc.save()
                    new_cc_id = cc.id

                u = user_profile.user
                c = Contact.objects.filter(contact_company=cc,
                                           first_name=u.first_name,
                                           last_name=u.last_name).first()
                new_c_id = None

                if c is None:
                    c = Contact(company=absolute,
                                created=now,
                                updated=now,
                                created_by=created_by,
                                first_name=u.first_name,
                                last_name=u.last_name,
                                email=u.email,
                                account='',
                                website='',
                                address='',
                                address2='',
                                city='',
                                zip='',
                                contact_company=cc,
                                contact_type=signups,
                                title=user_profile.signup_title()[:64])

                    c.save()
                    new_c_id = c.id

                # Get the new signup contact
                contact = Contact.objects.filter(id=new_c_id).first()
                if contact:
                    # Get the contact and add the contact_personnel for it
                    try:
                        contact_personnel = ContactPersonnel(company=absolute,
                                                             contact=contact,
                                                             first_name=u.first_name,
                                                             last_name=u.last_name,
                                                             email=u.email,
                                                             created=now,
                                                             updated=now)
                        contact_personnel.save()
                    except:
                        pass

                new_cc = ContactCompany.objects.filter(id=new_cc_id).first()
                if new_cc:
                    new_cc.primary_contact = c
                    new_cc.save()
                # - set lead source custom field to website or app signup
                try:
                    cfield_id = settings.DEFAULT_SIGNUP_CONTACT_ACCOUNT_LEAD_SCOURCE[acc_pos]
                    if cfield_id:
                        cfield = CField.objects.filter(company=absolute, id=cfield_id)[:1][0]
                        cfield_option = CFieldOption.objects.filter(cfield=cfield, id=option_id)[:1][0]
                        cfield_option_id = cfield_option.id
                        cfield_value = CFieldValue(cfield=cfield,
                                                   cf_value=cfield_option_id,
                                                   entity_id=new_c_id,
                                                   updated=now)
                        cfield_value.save()
                except:
                    pass

                try:
                    # New user signup date added in account details
                    new_signup_date_custom_field_id = settings.DEFAULT_SIGNUP_CONTACT_ACCOUNT_SIGNUP_DATE[acc_pos]
                    if new_signup_date_custom_field_id:
                        # Check and get custom field id
                        custom_field_id = CField.objects.filter(company=absolute,
                                                                id=int(new_signup_date_custom_field_id)).first()
                        new_signup_date_custom_field_value = CFieldValue(cfield=custom_field_id,
                                                                         cf_value=now.strftime('%m/%d/%Y'),
                                                                         entity_id=new_c_id,
                                                                         updated=now)
                        new_signup_date_custom_field_value.save()
                except:
                    pass

                # - set previous contact type to website signup
                try:
                    cfield_id = settings.DEFAULT_SIGNUP_CONTACT_ACCOUNT_PREV_CONTC[acc_pos]
                    if cfield_id:
                        cfield = CField.objects.filter(company=absolute, id=cfield_id)[:1][0]
                        cfield_value = CFieldValue(cfield=cfield,
                                                   cf_value=prev_contact,
                                                   entity_id=new_c_id,
                                                   updated=now)
                        cfield_value.save()
                except:
                    pass

                pt = PhoneType.objects.filter(name='Office')[:1][0]
                cp = ContactPhone.objects.filter(contact=c,
                                                 phone_number=user_profile.signup_phone()).first()

                if cp is None:
                    pp = re.compile('[^0-9]')

                    try:
                        phone_number = pp.sub('', user_profile.signup_phone())
                    except:
                        phone_number = ''

                    if len(phone_number) == 11 and phone_number[0] == '1':
                        phone_number = phone_number[1:11]
                    elif len(phone_number) > 10:
                        phone_number = phone_number[:10]

                    cp = ContactPhone.objects.filter(contact=c, phone_number=phone_number).first()
                    # Check and save phone number to contact if not saved
                    if cp is None and phone_number:
                        cp = ContactPhone(company=absolute,
                                          contact=c,
                                          phone_type=pt,
                                          phone_number=phone_number,
                                          created=now,
                                          updated=now)
                        cp.save()

                new_c = None
                if new_c_id:
                    new_c = Contact.objects.filter(id=new_c_id).first()
                if new_c:
                    new_c.default_phone = cp
                    new_c.save()
                # Add signup info as notes for new signup contact.
                note = """Referer Info:<br>
IP address information for %s,<br>
Recent Signups: <a href='%s/admin/cp/userprofile/?manager__exact=1'>%s/admin/cp/userprofile/?manager__exact=1</a><br>
IP Address: %s,<br>
Country: %s,<br>
City: %s,<br>
Location: %s,<br>
Timezone: %s,<br>
Platform: %s,<br>
Device: %s.<br>
                """% (user_profile.fullname(),
                      settings.APP_URL,
                      settings.APP_URL,
                      ip_info_dict['ip_add'],
                      ip_info_dict['country_name'],
                      ip_info_dict['city'],
                      ip_info_dict['location'],
                      ip_info_dict['timezone'],
                      platform,
                      device_type)

                cn = ContactNote.objects.filter(contact=c, note=note).first()
                if cn is None:
                    cn = ContactNote(company=absolute,
                                     contact=c,
                                     note=note.strip(),
                                     user=created_by,
                                     created=now)
                    cn.save()

def send_payment_received_email(user_profile=None, payment=None):
    if socket.gethostname().find('callproof') < 0 or socket.gethostname().find('dev') == 0:
        return

    company = payment.company

    body_text = """

Invoice payment made!

Logged-in User: %s

Company: %s

When: %s

Amount: %s

Recent Payemnts: https://app.callproof.com/tools/billing/payments/

""" % (user_profile.fullname(),
       company.name,
       timezone.localtime(timezone.now()).strftime('%Y/%m/%d %I:%M%p'),
       payment.amount)

    # Get the MailgunWrapper class
    mailgun_wrapper = MailgunWrapper(['robert@callproof.com', 'luke@callproof.com'],
                                     'CallProof Payment Received',
                                     body_text,
                                     body_text.replace('\n', '<br />'))
    # Send the email
    mailgun_wrapper.send_email()


def get_google_places(latitude, longitude, radius, type, name):
    pattern = 'https://maps.googleapis.com/maps/api/place/search/json?fields=%&location=%s,%s&radius=%s%s%s&key=%s'
    list = (constants.MAP_SEARCH_FIELDS, latitude, longitude, radius, type, name, settings.GA_SIMPLE_API)
    url = pattern % list
    req = urllib.request.Request(url)
    opener = urllib.request.build_opener(urllib.request.HTTPSHandler(debuglevel=0))
    a = None
    try:
        req = opener.open(req)
    except:
        req = None
    if req:
        reply = req.read()
        req.close()
        a = json.loads(reply)
    return a


def get_here_map_response(url):
    req = urllib.request.Request(url)
    opener = urllib.request.build_opener(urllib.request.HTTPSHandler(debuglevel=0))
    a = None
    try:
        req = opener.open(req)
    except:
        logger.error('Get here map response Error : %s', url, exc_info=sys.exc_info())
        req = None
    if req:
        reply = req.read()
        req.close()
        a = json.loads(reply)
    return a


def calc_distance(lat1, lon1, lat2, lon2):
    arc = None
    degrees_to_radians = math.pi / 180.0
    try:
        lat1 = float(lat1)
    except:
        lat1 = None
    try:
        lat2 = float(lat2)
    except:
        lat2 = None
    try:
        lon1 = float(lon1)
    except:
        lon1 = None
    try:
        lon2 = float(lon2)
    except:
        lon2 = None
    if lat1 and lat2 and lon1 and lon2:
        phi1 = (90.0 - lat1) * degrees_to_radians
        phi2 = (90.0 - lat2) * degrees_to_radians
        theta1 = lon1 * degrees_to_radians
        theta2 = lon2 * degrees_to_radians
        cos = (math.sin(phi1) * math.sin(phi2) * math.cos(theta1 - theta2) +
               math.cos(phi1) * math.cos(phi2))
        try:
            arc = math.acos(cos) * 3960
        except:
            arc = None
    return arc


def contact_images_path(instance, filename):
    now = timezone.localtime(timezone.now())

    f_parts = str(filename).split('.')
    e = f_parts[len(f_parts) - 1] if len(f_parts) > 0 else ''

    s = '%s%s' % (now, filename)
    h = hashlib.sha1(s.encode('utf-8')).hexdigest()

    fd = '%s/images/contact_images/%s/%s/%s/%s' % (settings.MEDIA_ROOT,
                                                   h[0:2],
                                                   h[2:4],
                                                   h[4:6],
                                                   h[6:8])

    try:
        os.makedirs(fd)
    except:
        pass

    try:
        os.chmod(fd, 0o777)
    except:
        pass

    # chmod parent dirs
    d = '%s/images/contact_images/%s/%s/%s' % (settings.MEDIA_ROOT, h[0:2], h[2:4], h[4:6])
    try:
        os.chmod(d, 0o777)
    except:
        pass

    d = '%s/images/contact_images/%s/%s' % (settings.MEDIA_ROOT, h[0:2], h[2:4])
    try:
        os.chmod(d, 0o777)
    except:
        pass

    d = '%s/images/contact_images/%s' % (settings.MEDIA_ROOT, h[0:2])
    try:
        os.chmod(d, 0o777)
    except:
        pass

    filepath = '%s.%s' % (h, e) if len(e) > 0 else h

    return '%s/%s' % (fd, filepath)


def title_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT, 'images', 'titles', str(instance.company_id), filename)


def event_type_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT,
                        'images', 'event_types', str(instance.company_id), filename)


def mms_image_path(instance, filename):
    return os.path.join('images', 'mms', str(instance.company_id), filename)


def user_profile_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT,
                        'images', 'user_profiles', str(instance.company_id), filename)


def badge_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT,
                        'images', 'badges', str(instance.company_id), filename)


def company_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT,
                        'images', 'companies', 'image', str(instance.id), filename)


def company_bg_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT,
                        'images', 'companies', 'bg_image', str(instance.id), str(instance.id))


def contact_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT,
                        'images', 'contacts', str(instance.company_id), filename)


def contact_personnel_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT,
                        'images', 'contacts', 'personnel', str(instance.id), filename)


def contact_type_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT,
                        'images', 'contact_types', str(instance.company_id), filename)


def point_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT, 'images', 'points', str(instance.company_id), filename)


def room_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT, 'images', 'rooms', str(instance.company_id), filename)


def business_card_image_path(instance, filename):
    return os.path.join(settings.MEDIA_ROOT, 'images', 'business_card', str(instance.company_id), filename)


def get_durations():
    return [['15', '15 minutes'],
            ['30', '30 minutes'],
            ['60', '1 hour'],
            ['120', '2 hours'],
            ['240', 'Half Day'],
            ['480', 'All Day']]


def get_months():
    return [['1', 'Jan'],
            ['2', 'Feb'],
            ['3', 'Mar'],
            ['4', 'Apr'],
            ['5', 'May'],
            ['6', 'Jun'],
            ['7', 'Jul'],
            ['8', 'Aug'],
            ['9', 'Sep'],
            ['10', 'Oct'],
            ['11', 'Nov'],
            ['12', 'Dec']]


def get_ampm():
    return ['AM', 'PM']


def get_exp_years():
    year = timezone.localtime(timezone.now()).year
    return [y for y in range(year, year + 6)]


def get_exp_months():
    months = []
    for m in range(1, 13):
        month = str(m)
        if len(month) == 1:
            month = '0%s' % month
        months.append([m, month])
    return months


def get_hours():
    return [str(h) for h in range(1, 13)]


def get_days():
    return [str(d) for d in range(1, 32)]


def get_years():
    n = timezone.localtime(timezone.now())

    d = n.date()
    yy = int(d.year)
    return [str(y) for y in range(yy, yy + 3)]


def get_minutes(step=None):
    if step is None:
        step = 15
    if step < 1:
        step = 1
    if step > 15:
        step = 15
    return [(('0%s' % m) if len(str(m)) == 1 else ('%s' % m)) for m in range(0, 59, step)]


def get_midnight():
    return timezone.localtime(timezone.now()).replace(hour=0, minute=0, second=0, microsecond=0)


def get_yesterday():
    return get_midnight() - timedelta(days=1)


def get_tomorrow():
    return get_midnight() + timedelta(days=1)


def get_nextsevendays():
    return get_midnight() + timedelta(days=7)


def get_monthfirstday():
    return get_midnight().replace(day=1)


def get_duration_time(duration):
    hours = '00'
    minutes = '00'
    seconds = '00'
    if duration >= 3600:
        hours = int(duration / 3600)
        minutes = int(duration % 3600 / 60)
        seconds = int(duration - (float(hours) * 3600) - (float(minutes) * 60))
    elif duration >= 60:
        minutes = int(duration / 60)
        seconds = int(duration - (float(minutes) * 60))
    else:
        seconds = int(duration)
    hours, minutes, seconds = str(hours), str(minutes), str(seconds)
    if len(hours) == 1:
        hours = "0%s" % hours
    if len(minutes) == 1:
        minutes = "0%s" % minutes
    if len(seconds) == 1:
        seconds = "0%s" % seconds
    if hours == '00' and minutes == '00' and seconds == '00':
        return 'Current'
    return "%s:%s:%s" % (hours, minutes, seconds)


def unique(seq, idfun=None):
    if idfun is None:
        def idfun(x): return x
    seen = {}
    result = []
    for item in seq:
        marker = idfun(item)
        if marker in seen:
            continue
        seen[marker] = 1
        result.append(item)
    return result


def create_default_account(company, now):
    try:
        dummy_cpm = Company.objects.get(pk=settings.DEFAULT_SIGNUP_UPDATE_ACCOUNT)
        dummy_cpm_id = dummy_cpm.id
    except:
        return False

    try:
        mkts = Market.objects.filter(company=dummy_cpm)
        for mkt in mkts:
            c_mkt = Market(company=company, name=mkt.name, deleted=mkt.deleted)
            c_mkt.save()
    except:
        pass
    ctype_map = {}
    try:
        cnct_types = ContactType.objects.filter(company=dummy_cpm)
        # Date : 23-10-2019
        # AIT - CAL -16 : WEB - PROJECT - Create new Contact Type "Internal Staff"
        # Desc : When a default company is created, contact types are copied from the dummy account
        # the reference contact type name also must be inserted inorder to prevent the deletion
        # of Internal staff record and identifying it even after renaming the record.
        # The records are copied in the same order as template account
        for cnct_type in cnct_types:
            cnt = ContactType(company=company,
                              name=cnct_type.name,
                              image=cnct_type.image,
                              is_default=cnct_type.is_default,
                              reference_contact_type_name=cnct_type.name,
                              position=cnct_type.position)
            cnt.save()
            ctype_map[cnct_type.id] = cnt.id
    except:
        pass

    try:
        mcs = MenuCust.objects.filter(company=dummy_cpm)
        for mc in mcs:
            c_mc = MenuCust(company=company,
                            menu=mc.menu,
                            name=mc.name,
                            hide=mc.hide,
                            cost=mc.cost)
            c_mc.save()
    except:
        pass

    try:
        mcs = MenuColCust.objects.filter(company=dummy_cpm)
        for mc in mcs:
            c_mc = MenuColCust(company=company,
                               menu_col=mc.menu_col,
                               name=mc.name,
                               hide=mc.hide,
                               cost=mc.cost)
            c_mc.save()
    except:
        pass

    try:
        mrcs = MenuRowCust.objects.filter(company=dummy_cpm)
        for mc in mrcs:
            c_mc = MenuRowCust(company=company,
                               menu_row=mc.menu_row,
                               name=mc.name,
                               hide=mc.hide,
                               cost=mc.cost)
            c_mc.save()
    except:
        pass
    try:
        mrcs = MenuURLCust.objects.filter(company=dummy_cpm)
        for mc in mrcs:
            c_mc = MenuURLCust(company=company,
                               menu_url=mc.menu_url,
                               name=mc.name,
                               hide=mc.hide,
                               cost=mc.cost)
            c_mc.save()
    except:
        pass

    cpeoplerole = {}
    try:
        prs = PeopleRole.objects.filter(company=dummy_cpm)
        for pr in prs:
            c_pr = PeopleRole(company=company, name=pr.name)
            c_pr.save()
            cpeoplerole[pr] = c_pr
    except:
        pass
    try:
        opptypes = OppType.objects.filter(company=dummy_cpm)
        for opptype in opptypes:
            ot = OppType(company=company, name=opptype.name, position=opptype.position)
            ot.save()
    except:
        pass
    followup_type_list = {}
    try:
        followuptypes = FollowupType.objects.filter(company=dummy_cpm)
        for followuptype in followuptypes:
            ft = FollowupType(company=company,
                              name=followuptype.name,
                              position=followuptype.position,
                              is_default=followuptype.is_default)
            ft.save()
            followup_type_list[followuptype] = ft
    except:
        pass
    try:
        oppstages = OppStage.objects.filter(company=dummy_cpm)
        for oppstage in oppstages:
            fs = OppStage(company=company,
                          name=oppstage.name,
                          fg_color=oppstage.fg_color,
                          bg_color=oppstage.bg_color,
                          fg_color2=oppstage.fg_color2,
                          bg_color2=oppstage.bg_color2,
                          position=oppstage.position,
                          probability=oppstage.probability,
                          lock=oppstage.lock)
            fs.save()
    except:
        pass
    # - saving custom fields
    cfield_list = {}
    try:
        cfields = CField.objects.filter(company=dummy_cpm).order_by('id')

        for cfield in cfields:
            cf = CField(company=company,
                        name=cfield.name,
                        cfield_table=cfield.cfield_table,
                        cfield_type=cfield.cfield_type,
                        position=cfield.position,
                        rfield_id=cfield.rfield_id,
                        points=cfield.points, )
            cf.save()
            cfield_list[cfield] = cf
            try:
                if cfield.cfield is not None and cfield.cfield and cfield.cfield != '':
                    cf.cfield = cfield_list[cfield.cfield]
                    cf.save()
            except:
                pass

            cfield_options = CFieldOption.objects.filter(cfield=cfield)
            cfield_option_list = {}
            for cfield_option in cfield_options:
                co = CFieldOption(name=cfield_option.name,
                                  cfield=cf,
                                  position=cfield_option.position)
                co.save()
                cfield_option_list[str(cfield_option.id)] = str(co.id)
                if cfield_option.id == cfield.cfield_option_default_id:
                    cf.cfield_option_default_id = co.id
                    cf.save()
    except:
        pass
    event_form_list = {}
    try:
        # - saving event form
        eventforms = EventForm.objects.filter(company=dummy_cpm)
        for eventform in eventforms:
            ef = EventForm(company=company,
                           name=eventform.name,
                           post_back_url=eventform.post_back_url,
                           post_back_secret=eventform.post_back_secret,
                           post_back_method=eventform.post_back_method,
                           position=eventform.position,
                           points=eventform.points,
                           is_schedule_followup=eventform.is_schedule_followup,
                           send_email_to_rep=eventform.send_email_to_rep,
                           event_form_treat_as_id=eventform.event_form_treat_as_id,
                           is_after_call_form=eventform.is_after_call_form)
            ef.save()
            event_form_list[eventform] = ef
            # - saving contact type list
            try:
                efctypes = EventFormContactType.objects.filter(event_form=eventform)
                for efctype in efctypes:
                    try:
                        ctype_id = ctype_map[efctype.contact_type_id]
                    except:
                        ctype_id = None
                    efcs = EventFormContactType(company=company,
                                                event_form=ef,
                                                contact_type_id=ctype_id)
                    efcs.save()
            except:
                pass
            # - saving event form email
            try:
                eventformemails = EventFormEMail.objects.filter(event_form=eventform)
                for eventformemail in eventformemails:
                    efe = EventFormEMail(event_form=ef,
                                         email=eventformemail.email)
                    efe.save()
            except:
                pass
            # - event form feilds
            try:
                # - link eventform with cfield
                for eventformcfield in EventFormCField.objects.filter(event_form=eventform):
                    try:
                        efc = EventFormCField(event_form=ef,
                                              cfield=cfield_list[eventformcfield.cfield],
                                              position=eventformcfield.position)
                        efc.save()
                    except:
                        pass
            except:
                pass
    except:
        pass
    cml_dic = {}
    try:
        cmls = ContactMenuList.objects.filter(company=dummy_cpm)
        for cml in cmls:
            cml_c = ContactMenuList(company=company,
                                    name=cml.name,
                                    is_active=cml.is_active)
            cml_c.save()
            cml_dic[cml.id] = cml_c.id

        cms = ContactMenu.objects.filter(company=dummy_cpm)

        for cm in cms:
            try:
                try:
                    cml_id = cml_dic[cm.contactmenulist.id]
                except:
                    cml_id = None
                try:
                    cml_ef = event_form_list[cm.event_form]
                except:
                    cml_ef = None
                cm_c = ContactMenu(company=company,
                                   name=cm.name,
                                   type=cm.type,
                                   position=cm.position,
                                   is_hide=cm.is_hide,
                                   event_form=cml_ef,
                                   location=cm.location,
                                   contactmenulist_id=cml_id)
                cm_c.save()
            except:
                pass
    except:
        pass

    pl_list_dict = {}
    try:
        for dummy_li in PlacesCategoryList.objects.filter(company=dummy_cpm):
            pl_li = PlacesCategoryList(name=dummy_li.name, company=company)
            pl_li.save()
            pl_list_dict[dummy_li] = pl_li

        for dummy_cat in PlacesCategory.objects.filter(company=dummy_cpm):
            cat = PlacesCategory(name=dummy_cat.name,
                                 company=company,
                                 cat_list=pl_list_dict[dummy_cat.cat_list],
                                 hide=dummy_cat.hide)
            cat.save()
            CategorySic.objects.bulk_create([
                CategorySic(category=cat, sic=dummy_sic.sic)
                for dummy_sic in CategorySic.objects.filter(category=dummy_cat)
            ])
    except:
        pass

    other_title = ''
    try:
        titles = Title.objects.filter(company=dummy_cpm)

        for title in titles:
            try:
                cml_id = cml_dic[title.contactmenulist.id]
            except:
                cml_id = None
            try:
                places_list = pl_list_dict[title.places_cat_list]
            except:
                places_list = None
            tle = Title(company=company,
                        name=title.name,
                        image=title.image,
                        contactmenulist_id=cml_id,
                        places_cat_list=places_list)
            tle.save()
            if title.name.lower() == 'other':
                other_title = tle
    except:
        pass
    contactslist = {}
    select = CFieldType.objects.filter(name='select')[:1][0]
    radio = CFieldType.objects.filter(name='radio')[:1][0]
    try:
        up = UserProfile.objects.filter(company=company).order_by('id').first()
        if other_title:
            up.title = other_title
            up.contactmenulist = other_title.contactmenulist
            up.save()

        created_by = None
        if up:
            created_by = up.user
        cnctcmps = ContactCompany.objects.filter(company=dummy_cpm).order_by('id')
        for cnctcmp in cnctcmps:
            cc = ContactCompany(company=company, name=cnctcmp.name, created=now, updated=now)
            cc.save()
            cncts = Contact.objects.filter(company=dummy_cpm,
                                           contact_company=cnctcmp).order_by('id')
            for cnct in cncts:
                try:
                    ctype_id = ctype_map[cnct.contact_type_id]
                except:
                    ctype_id = None
                c = Contact(company=company,
                            contact_type_id=ctype_id,
                            first_name=cnct.first_name,
                            last_name=cnct.last_name,
                            email=cnct.email,
                            city=cnct.city,
                            account=cnct.account,
                            state=cnct.state,
                            zip=cnct.zip,
                            title=cnct.title,
                            created_by=created_by,
                            address=cnct.address,
                            address2=cnct.address2,
                            country_id=cnct.country_id,
                            website=cnct.website,
                            latitude=cnct.latitude,
                            longitude=cnct.longitude,
                            image=cnct.image,
                            do_not_sms=cnct.do_not_sms,
                            created=now,
                            updated=now,
                            contact_company=cc, )
                try:
                    c.save()
                except:
                    break

                contactslist[cnct.id] = c.id
                try:
                    cr = ContactRep(contact=c,
                                    user=created_by,
                                    created=now)
                    cr.save()
                except:
                    pass
                try:
                    cfieldvalues = CFieldValue.objects.filter(entity_id=cnct.id).order_by('id')
                    for cfieldvalue in cfieldvalues:
                        try:
                            cfieldvalue.cf_value = cfield_option_list[str(cfieldvalue.cf_value)]
                        except:
                            if cfieldvalue.cfield.cfield_type_id == select.id or \
                                    cfieldvalue.cfield.cfield_type_id == radio.id:
                                continue

                        if cfieldvalue.cfield in cfield_list:
                            cfv = CFieldValue(cfield=cfield_list[cfieldvalue.cfield],
                                              cf_value=cfieldvalue.cf_value,
                                              entity_id=c.id,
                                              updated=now)
                            cfv.save()
                except:
                    pass
                try:
                    pers = ContactPersonnel.objects.filter(company=dummy_cpm, contact=cnct)
                    per_list = {}
                    for per in pers:
                        try:
                            peoplerole = cpeoplerole[per.peoplerole]
                        except:
                            peoplerole = None
                        c_per = ContactPersonnel(company=company,
                                                 contact=c,
                                                 first_name=per.first_name,
                                                 last_name=per.last_name,
                                                 email=per.email,
                                                 personnel_notes=per.personnel_notes,
                                                 cell_phone=per.cell_phone,
                                                 title=per.title,
                                                 created=now,
                                                 updated=now,
                                                 peoplerole=peoplerole,
                                                 image=per.image,
                                                 is_disabled=per.is_disabled)
                        c_per.save()
                        per_list[per] = c_per
                except:
                    pass

                try:
                    cnct_phones = ContactPhone.objects.filter(company=dummy_cpm, contact=cnct)
                    for cnct_phone in cnct_phones:
                        cp = ContactPhone(company=company,
                                          contact=c,
                                          phone_type=cnct_phone.phone_type,
                                          phone_number=cnct_phone.phone_number,
                                          created=now,
                                          updated=now)
                        cp.save()
                        cp_pers = cnct_phone.get_personnels()
                        for cp_per in cp_pers:
                            try:
                                per = per_list[cp_per]
                            except:
                                per = None
                            cpp = ContactPhonePersonnel(
                                contactphone=cp,
                                personnel=per
                            )
                            cpp.save()
                except:
                    pass
                try:
                    cnct_notes = ContactNote.objects.filter(company=dummy_cpm, contact=cnct)
                    for cnct_note in cnct_notes:
                        note = ContactNote(company=company,
                                           contact=c,
                                           user=created_by,
                                           note=cnct_note.note,
                                           created=now)
                        note.save()
                except:
                    pass

                try:
                    followups = Followup.objects.filter(contact=cnct)
                    for f in followups:
                        start_date = f.start + relativedelta(
                            years=3)  # -Create a followup for 3 years into the future using
                        try:
                            ft = followup_type_list[f.followup_type]
                        except:
                            ft = None
                        followup = Followup(user=created_by,
                                            contact=c,
                                            start=start_date,
                                            duration=f.duration,
                                            notes=f.notes,
                                            completed=f.completed,
                                            updated=now,
                                            created=now,
                                            followup_type=ft)
                        followup.save()
                        created_by.userprofile.add_event(name='task_scheduled',
                                                         contact=c,
                                                         start=now,
                                                         followup=followup)
                        for fp in FollowupPersonnel.objects.filter(followup=f):
                            c_fp = FollowupPersonnel(followup=followup,
                                                     personnel=per_list[fp.personnel])
                            c_fp.save()
                except:
                    pass

                # - create and submitting the eventform
                try:
                    contact_event_forms = ContactEventForm.objects.filter(company=dummy_cpm,
                                                                          contact=cnct)
                    for contact_event_form in contact_event_forms:
                        try:
                            ef = event_form_list[contact_event_form.event_form]
                        except:
                            break
                        cef = ContactEventForm(company=company,
                                               user=created_by,
                                               contact=c,
                                               event_form=ef,
                                               created=now)
                        cef.save()
                        cfieldvalues = CFieldValue.objects.filter(entity_id=contact_event_form.id).order_by('id')
                        for cefp in ContactEventFormPersonnel.objects \
                                .filter(contacteventform=contact_event_form):
                            c_fp = ContactEventFormPersonnel(contacteventform=cef,
                                                             personnel=per_list[cefp.personnel])
                            c_fp.save()
                        for cfieldvalue in cfieldvalues:
                            if cfieldvalue.cf_value in cfield_option_list:
                                cfieldvalue.cf_value = cfield_option_list[cfieldvalue.cf_value]
                            if cfieldvalue.cfield in cfield_list:
                                cfv = CFieldValue(cfield=cfield_list[cfieldvalue.cfield],
                                                  cf_value=cfieldvalue.cf_value,
                                                  entity_id=cef.id,
                                                  updated=now)
                                cfv.save()
                        cef.award_points()
                        from django.http import HttpRequest
                        req = HttpRequest()
                        req.user_profile = up
                        req.user = up.user
                        req.company = company
                        send_eform_emails(req, cef, False, c.contact_company)
                        do_eform_post_back(req, cef)
                        up.add_event(name='event_form', start=now, contact=c, created=now, cef=cef)
                except:
                    pass
    except:
        pass
    try:
        badges = Badge.objects.filter(company=dummy_cpm)
        for badge in badges:
            b = Badge(company=company, name=badge.name, points=badge.points, image=badge.image)
            b.save()
    except:
        pass
    try:
        points = Point.objects.filter(company=dummy_cpm)
        for point in points:
            p = Point(company=company, name=point.name, value=point.value, image=point.image)
            p.save()
    except:
        pass
    signup_event = ''
    try:
        eventtypes = EventType.objects.filter(company=dummy_cpm)
        for eventtype in eventtypes:
            et = EventType(company=company,
                           name=eventtype.name,
                           desc=eventtype.desc,
                           image=eventtype.image,
                           updated=now)
            et.save()
            if eventtype.name == 'signup':
                signup_event = et
            eventtypepts = EventTypePoint.objects.filter(event_type=eventtype)
            for eventtypept in eventtypepts:
                p = Point.objects.filter(company=company, value=eventtypept.point.value)[:1][0]
                etp = EventTypePoint(event_type=et, point=p, created=now, updated=now)
                etp.save()
    except:
        pass

    try:
        event_dic = collections.OrderedDict()
        event_dic[0] = 'Welcome to CallProof!  Thank you for creating an account'
        event_dic[1] = 'Login with the Web Version to Customize CallProof'
        event_dic[2] = 'Check Your Tasks in the Lower Right Corner of Mobile App'

        if signup_event:
            for indx, event in list(event_dic.items()):
                tme = now + relativedelta(minute=indx)
                evt = Event(
                    company=company,
                    event_type=signup_event,
                    message=event,
                    user=created_by,
                    start=tme,
                    created=tme,
                    popular=tme
                )
                evt.save()
    except:
        pass

    return True


def add_default_events(company=None):
    company = Company.objects.filter(id=company.id).first()
    m = Membership.objects.filter(company=company).first()
    if m:
        return

    now = timezone.localtime(timezone.now())
    try:
        create_default_account(company, now)
    except:
        pass

    billingopt = BillingOpt.objects.all().order_by('id')[:1][0]
    plan = Plan.objects.filter(price=0.00)[:1][0]

    m = Membership(company=company,
                   plan=plan,
                   billing_opt=billingopt,
                   billing_date=get_billing_date(),
                   created=now,
                   updated=now)
    m.save()

    for k in get_campaign_keys():
        cs = CompanySetting(company=company, name=k, value='1', updated=now)
        cs.save()

    for name in get_twilio_call_results():
        tcr = TwilioCallResult(company=company, result=name)
        tcr.save()


def change_timezone_manually(timestamp, timezone_name):
    import pytz

    local_tz = pytz.timezone('UTC')
    local_timestamp = local_tz.localize(timestamp)
    utc_timestamp = local_timestamp.astimezone(pytz.utc)
    converted_timestamp = utc_timestamp.astimezone(pytz.timezone(timezone_name))

    return converted_timestamp


def get_datetime_by_user_timezone(user_id):
    user = User.objects.filter(id=user_id).first()
    if user:
        try:
            up = user.userprofile
        except:
            up = None

        if up:
            timezone_name = up.get_user_timezone()
            timezone.activate(pytz.timezone(timezone_name))

            now = timezone.localtime(timezone.now())

            return now
        else:
            now = timezone.localtime(timezone.now())
    else:
        now = timezone.localtime(timezone.now())

    return now


def get_aware_datetime_by_user_timezone(dtime, user_id):
    user = User.objects.filter(id=user_id).first()
    if user:
        try:
            up = user.userprofile
        except:
            up = None

        if up:
            timezone_name = up.get_user_timezone()
            timezone.activate(pytz.timezone(timezone_name))
            aware_dtime = timezone.make_aware(dtime, timezone.get_current_timezone())
            return aware_dtime
        else:
            aware_dtime = timezone.localtime(dtime, timezone.get_default_timezone())
    else:
        aware_dtime = timezone.localtime(dtime, timezone.get_default_timezone())

    return aware_dtime


def get_ip_info(request):
    client_ip = request.POST.get("ip_addr", None)

    # In some situations, the ip_address may be passed as 'undefined', which will cause this to throw an exception
    if client_ip == 'undefined':
        client_ip = None

    if not client_ip:
        x_forwarded_for = request.META.get('HTTP_X_FORWARDED_FOR')
        if x_forwarded_for:
            client_ip = x_forwarded_for.split(',')[-1].strip()
        else:
            client_ip = request.META.get('REMOTE_ADDR')

    # If we weren't able to identify an IP address for the client request, then skip over this
    if not client_ip:
        return None

    url = 'http://ipinfo.io/{}/json'.format(client_ip)
    try:
        response = urlopen(url)
    except urllib.error.HTTPError:
        logger.error('get_ip_info: %s', url, exc_info=sys.exc_info())
        return None

    # parse the response
    data = json.load(response)

    IP = data['ip']
    org = data['org']
    city = data['city']
    country = data['country']
    region = data['region']
    timezone = data['timezone']
    location = data['loc']

    if data:
        ip_info_dict = {}
        ip_info_dict['ip_add'] = IP
        ip_info_dict['timezone'] = timezone  # - not getting in python3
        try:
            ip_info_dict['country_name'] = country
        except:
            ip_info_dict['country_name'] = ''
        try:
            ip_info_dict['city'] = city
        except:
            ip_info_dict['city'] = ''
        try:
            ip_info_dict['location'] = location
        except:
            ip_info_dict['location'] = ''
    else:
        ip_info_dict = None
    return ip_info_dict


# send push notification
def send_push_notification_all(legacy_keys, registration_ids, data_message):
    for key in legacy_keys:
        try:
            push_service = FCMNotification(api_key=key)
            result = push_service.notify_multiple_devices(registration_ids=registration_ids,
                                                          data_message=data_message)
        except Exception:
            result = False
    return result


# send push notification web
def send_push_notification_web(key, registration_id, message_title,
                               message_body, click_action=None):
    try:
        push_service = FCMNotification(api_key=key)
        result = push_service.notify_single_device(registration_id=registration_id,
                                                   message_title=message_title,
                                                   message_body=message_body,
                                                   click_action=click_action)
    except:
        result = False
    return result


# send push notification
def send_push_notification_iphone(legacy_key, registration_ids, message_body):
    try:
        push_service = FCMNotification(api_key=legacy_key)
        result = push_service.notify_multiple_devices(registration_ids=registration_ids,
                                                      message_body=message_body)
    except:
        result = False
    return result


def send_push_notification_dealer_ios(legacy_key, registration_ids, message_body, data_message):
    try:
        push_service = FCMNotification(api_key=legacy_key)
        result = push_service.notify_multiple_devices(registration_ids=registration_ids,
                                                      message_body=message_body,
                                                      data_message=data_message)
    except:
        result = False
    return result


def contact_type_obj(request, name):
    ct = ContactType.objects.filter(company=request.company, name=name)[:1]
    try:
        ct = ct[0]
    except:
        # Date : 23-10-2019
        # AIT - CAL -16 : WEB - PROJECT - Create new Contact Type "Internal Staff"
        # Desc : reference_contact_type_name name are added.
        ct = ContactType(company=request.company, name=name, reference_contact_type_name=name)
        ct.save()
    return ct


def get_appropriate_contact_type(request, contact_phone, contact, cr):
    from cfields.templatetags.cfields_extras import process_custom_fields
    ct = contact_type_obj(request, contact.contact_type.name)
    post = {}
    cf = CField.objects.filter(name='Source', company=request.company)[0]
    post['entity'] = contact.id
    now = timezone.localtime(timezone.now())
    try:
        if contact_phone.contact_type:
            pass
        else:
            contact_phone.contact_type = contact.contact_type
            contact_phone.save()
    except:
        contact_phone.contact_type = contact.contact_type
        contact_phone.save()

    if contact_phone.contact_type.name == 'Follow-Up Calls':
        ct = contact_type_obj(request, '2nd Follow-Up Calls')
    elif contact_phone.contact_type.name == '2nd Follow-Up Calls':
        followup__arr1 = ['Talked to Customer - Completed', 'Left Voicemail']
        followup__arr2 = ['No Answer', 'Talked to Customer - Follow Up Required']
        followup__arr3 = ['Set Appointment']

        if cr.result in followup__arr1:
            ct = contact_type_obj(request, 'Current Customers')
            post['cf_' + str(cf.id)] = ''
            process_custom_fields(post, 'contact', request.company)
        elif cr.result in followup__arr2:
            ct = contact_type_obj(request, '2nd Follow-Up Calls')
        elif cr.result in followup__arr3:
            ct = contact_type_obj(request, 'General Leads')
    elif contact_phone.contact_type.name == 'Facebook Leads':
        fb_arr1 = ['Set Appointment',
                   'Left Voicemail',
                   'No Answer',
                   'Talked to Customer - Follow Up Required',
                   'Talked to Customer - Completed']

        if cr.result in fb_arr1:
            ct = contact_type_obj(request, 'Facebook Leads')

        cfo = CFieldOption.objects.filter(cfield_id=cf.id, name='Facebook')[0]
        post['cf_' + str(cf.id)] = cfo.id
        process_custom_fields(post, 'contact', request.company)

        # save last contacted on cpex_facebookcontacts
        from cpex.models import FacebookContacts
        fc = FacebookContacts.objects.filter(phone_number=contact_phone.phone_number).using('google_ds').order_by(
            '-id')[:1]
        try:
            fc = fc[0]
        except:
            fc = None

        if fc:
            try:
                fc.last_contacted = now
                fc.save(using='google_ds')
            except:
                pass
    elif contact_phone.contact_type.name == 'Current Customers':
        cc_arr1 = ['Talked to Customer - Completed',
                   'Left Voicemail',
                   'No Answer',
                   'Talked to Customer - Follow Up Required']
        cc_arr2 = ['Set Appointment']

        if cr.result in cc_arr1:
            ct = contact_type_obj(request, 'Current Customers')

        elif cr.result in cc_arr2:
            ct = contact_type_obj(request, 'General Leads')
            if contact_phone.call_count:
                if contact_phone.call_count == 3:
                    ct = contact_type_obj(request, 'Current Customers')  # increase call counter
                    contact_phone.call_count = 0
                else:
                    contact_phone.call_count = contact_phone.call_count + 1
            else:
                contact_phone.call_count = 1
            contact_phone.save()
        cfo = CFieldOption.objects.filter(cfield_id=cf.id, name='Current Customer')[0]
        post['cf_' + str(cf.id)] = cfo.id
        process_custom_fields(post, 'contact', request.company)

    if contact_phone.contact_type.name == '2nd Follow-Up Calls':
        if cr.result not in followup__arr2:
            contact.last_contacted = now
            contact.contact_type = ct
            contact.save()
            contact_phone.last_contacted = now
            contact_phone.contact_type = ct
            contact_phone.save()
    else:
        contact.last_contacted = now
        contact.contact_type = ct
        contact.save()
        contact_phone.last_contacted = now
        contact_phone.contact_type = ct
        contact_phone.save()

    return ct


def generate_csv(filename, headers, data_list, **kwargs):
    # Generate CSV Filepath
    filename = EfsFilenameBuilder.generate_filepath(filename)
    with open(filename, 'w') as file:
        writer = csv.writer(file)
        writer.writerow(headers)
        for data in data_list:
            content = data.get_report_data_list(**kwargs)
            writer.writerow(content)


class Download(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    version = models.IntegerField()
    created = models.DateTimeField()

    def __str__(self):
        return '%s %s %s' % (self.user.userprofile.fullname, self.version, self.created)


class Provider(models.Model):
    name = models.CharField(max_length=16, unique=True)

    def __str__(self):
        return '%s' % self.name


class Country(models.Model):
    name = models.CharField(max_length=50, unique=True)

    def __str__(self):
        return '%s' % self.name

    class Meta:
        verbose_name_plural = 'countries'


class State(models.Model):
    name = models.CharField(max_length=32)
    abbr = models.CharField(max_length=3)
    province = models.CharField(max_length=32)

    def __str__(self):
        return '%s' % self.name

    class Meta:
        unique_together = ('name', 'abbr', 'province')

    @staticmethod
    def provinces(states):
        provinces = {}
        state_list = []
        try:
            for state in states:
                try:
                    provinces[state.province].append({'id': state.id, 'value': state.name})
                except:
                    provinces[state.province] = [{'id': state.id, 'value': state.name}]
            for province in provinces:
                state_list.append({"province": province, "states": provinces[province]})
        except:
            pass
        return state_list


# To get the user country name
def get_user_country_name(user_profile):
    user_profile = UserProfile.objects.filter(id=user_profile.id).first()

    if user_profile and user_profile.country:
        return user_profile.country.name
    else:
        user_company = Company.objects.filter(id=user_profile.company.id).first()
        if user_company and user_company.country:
            return user_company.country.name

    country = Country.objects.get(name='United States')
    return country.name


class Location(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    provider = models.ForeignKey(Provider, null=True, blank=True, on_delete=models.SET_NULL)
    altitude = models.IntegerField(null=True, blank=True)
    accuracy = models.IntegerField(null=True, blank=True)
    latitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    longitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    speed = models.DecimalField(max_digits=5, decimal_places=2, null=True, blank=True)
    bearing = models.DecimalField(max_digits=5, decimal_places=2, null=True, blank=True)
    address = models.CharField(max_length=80, null=True, blank=True)
    city = models.CharField(max_length=64, null=True, blank=True)
    state = models.ForeignKey(State, null=True, blank=True, on_delete=models.SET_NULL)
    zip = models.CharField(max_length=10, null=True, blank=True)
    last_geocode = models.DateTimeField(null=True, blank=True)
    geocode_count = models.IntegerField(null=True, blank=True, default=0)
    created = models.DateTimeField()
    geo_track_type = models.CharField(max_length=64, null=False, default='regular')
    link_id = models.CharField(max_length=64, null=False)

    def __str__(self):
        return '%s %s %s,%s' % (
            self.user.first_name,
            self.user.last_name,
            self.latitude,
            self.longitude)

    def full_address(self):
        state = self.state.abbr if self.state else ''
        if state == 'null':
            state = ''
        address = self.address if self.address else ''
        if address == 'null':
            address = ''
        city = self.city if self.city else ''
        if city == 'null':
            city = ''
        zip = self.zip if self.zip else ''
        if zip == 'null':
            zip = ''
        addr = '%s %s %s %s' % (address, city, state, zip)
        addr = addr.replace('  ', ' ').strip()
        if len(addr) == 0:
            addr = 'Unknown'
        return addr

    def here_reverse_geocode(self):
        output = '\nlocation: %s' % self

        if self.latitude and self.longitude:

            status_code, response_data = reverse_geo_code_here_api(self.latitude, self.longitude)

            if status_code != 200 or not response_data or 'items' not in response_data or len(response_data['items']) == 0:
                heregeocodelog(response_data)
            else:
                here_address = response_data['items'][0]['address']
                if here_address:
                    output += here_address.get('label', '')
                    house_number = here_address.get('houseNumber', '')
                    building = here_address.get('building', '')
                    street = here_address.get('street', '')
                    city = here_address.get('city', '')
                    state_name = here_address.get('state', '')
                    zip = here_address.get('postalCode', '')
                    zip = zip.split('-')[0] if '-' in zip else zip

                    address = f'{house_number}{building}{street}'.strip()

                    province_name = here_address.get('countryName') if 'countryName' in here_address else 'United States '
                    state = State.objects.filter(abbr=state_name,
                                                 province=province_name).first() if state_name != '' else None

                    if address or city or state or zip:
                        self.address = address
                        self.city = city
                        self.state = state
                        self.zip = zip

                    new_geocode_count = self.geocode_count + 1 if self.geocode_count else 1

                    self.geocode_count = new_geocode_count

                    if self.last_geocode:
                        self.last_geocode = self.last_geocode + timedelta(days=(2 * new_geocode_count))
                    else:
                        self.last_geocode = timezone.localtime(timezone.now()) + \
                                            timedelta(days=(2 * new_geocode_count))
                    self.save()

        return output


class Company(models.Model):
    name = models.CharField(unique=True, max_length=64)
    address = models.CharField(max_length=80, null=True, blank=True)
    address2 = models.CharField(max_length=80, null=True, blank=True)
    city = models.CharField(max_length=64, null=True, blank=True)
    state = models.ForeignKey(State, null=True, blank=True, on_delete=models.SET_NULL)
    zip = models.CharField(max_length=10, null=True, blank=True)
    country = models.ForeignKey(Country, null=True, blank=True, on_delete=models.SET_NULL)
    latitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    longitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    website = models.CharField(max_length=80, null=True, blank=True)
    image = ImageField(upload_to=company_image_path, null=True, blank=True)
    bg_image = ImageField(upload_to=company_bg_image_path, null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    last_activity = models.DateTimeField()
    contact_map_hours = models.IntegerField(default=12)
    activity_30 = models.IntegerField()
    activity_90 = models.IntegerField()
    balance = models.DecimalField(max_digits=7, decimal_places=2)
    disabled = models.NullBooleanField(null=True, blank=True)
    gryphon = models.NullBooleanField(null=True, blank=True)
    gryphon_number = models.CharField(max_length=10, null=True, blank=True)
    gryphon_pin = models.CharField(max_length=10, null=True, blank=True)
    gryphon_campaign = models.CharField(max_length=10, null=True, blank=True)
    twilio = models.BooleanField(default=False)
    twilio_record = models.BooleanField(default=False)
    twilio_conference = models.BooleanField(default=False)
    dealer = models.BooleanField(default=False)
    is_carrier_caller_enabled = models.BooleanField(default=False, blank=True)
    is_openvbx_enabled = models.BooleanField(default=False, blank=True)
    is_twilio_client_forward_enable = models.BooleanField(default=False, blank=True)
    is_app_call_without_beacon = models.BooleanField(default=False, blank=True)
    is_beacon_enabled = models.BooleanField(default=False, blank=True)
    is_copy_note = models.BooleanField(default=False, blank=True)
    hide_personal_calls = models.BooleanField(default=False)
    transaction_months = models.IntegerField(default=18)
    transaction_commission = models.DecimalField(max_digits=6, decimal_places=2, default=0.00)
    call_buy_days = models.IntegerField(default=14)
    referer_url = models.ForeignKey('RefererURL', null=True, blank=True, on_delete=models.SET_NULL)
    sales_rep_single_mode = models.NullBooleanField(null=True, blank=True)
    check_email = models.BooleanField(default=True)
    beep_minutes = models.IntegerField(default=15)
    imap_long_check_days = models.IntegerField(default=30)
    new_events = models.BooleanField(default=True)
    callproof_rep_name = models.CharField(max_length=80, null=True, blank=True)
    is_login_limit = models.BooleanField(default=False, blank=False)
    is_call_forward_to_carrier = models.BooleanField(default=False, blank=True)
    is_call_forward_to_default_salesrep = models.BooleanField(default=False, blank=True)
    is_youtube_video_enabled = models.BooleanField(default=False, blank=True)
    people_tab = models.BooleanField(default=True)
    is_green_button_enabled = models.BooleanField(default=True)
    is_blue_button_enabled = models.BooleanField(default=True)
    is_yellow_button_enabled = models.BooleanField(default=True)
    is_account_inc = models.BooleanField(default=False)
    account_inc = models.IntegerField(default=0)
    opp_sign = models.CharField(default='', blank=True, null=True, max_length=10)
    is_custom_field_required = models.BooleanField(default=False)
    is_event_form_required = models.BooleanField(default=False)
    is_number_of_stats_shown = models.BooleanField(default=False)
    is_logs_enabled = models.BooleanField(default=True)
    primary_location_search_type = models.ForeignKey(LocationSearchType,
                                                     default=2,
                                                     on_delete=models.CASCADE)
    is_recommended_followup_enabled = models.BooleanField(default=True)
    is_task_widget_enabled = models.BooleanField(default=True)
    is_opportunity_widget_enabled = models.BooleanField(default=True)
    is_suspended = models.BooleanField(default=False)
    is_videomessage_enabled = models.BooleanField(default=False)
    is_2fa_enabled = models.BooleanField(default=False, null=True, blank=True)
    is_business_card_widget_enabled = models.BooleanField(default=True)
    is_ai_enabled = models.BooleanField(default=False)

    def __str__(self):
        return '%s' % self.name

    def is_retail(self):
        return self.id in [26, 6177]

    def get_roles(self):
        return PeopleRole.objects.filter(company=self).order_by('name')

    def merge_people_running(self):
        if MergePeopleDuplicates.objects \
                .filter(company=self) \
                .exclude(status='completed').count() > 0:
            return True
        else:
            return False

    def people_conversion_running(self):
        if PeopleRun.objects.filter(company=self).exclude(status='completed').count() > 0:
            return True
        else:
            return False

    def total_paid(self):
        total = 0
        for i in Invoice.objects.filter(company=self):
            total += i.payments()
        return total

    def recent_payment_date(self):
        payments = Payment.objects.filter(company=self).order_by('-created')
        if len(payments) > 0:
            payments = payments[0]
            date = payments.created
        else:
            date = "NA"
        return date

    def has_image_field(self):
        for cf in CField.objects.filter(company=self):
            try:
                cft = cf.cfield_type
            except:
                cft = None
            if cft and cft.name == 'image':
                return True
        return False

    def get_available_public_phones(self):
        phones = []
        for tp in TwilioPhoneNumber.objects.filter(company=self):
            if tp.tollfree or tp.deleted:
                continue

            atp = AutotextTwilioPhone.objects.filter(company=self, twilio_phone=tp).first()
            if atp:
                continue

            phones.append(tp)

        return phones

    def opp_close_date_rename(self):
        cs = CompanySetting.objects.filter(company=self, name='opp_close_date_rename').first()
        if cs and cs.value != '':
            return cs.value
        return 'Close Date:'

    def get_events_list(self):
        where = 'user_id IN (%s)' % ','.join(self.user_ids())
        return Event.objects.extra(where=[where]).order_by('start')

    def get_contact_types_list(self):
        return ContactType.objects.filter(company=self).order_by('id')

    def get_contacts_list(self):
        return Contact.objects.filter(company=self).order_by('id')

    def get_contact_phones_list(self):
        return ContactPhone.objects.filter(company=self).order_by('id')

    def get_google_place_searches(self):
        return GooglePlaceSearch.objects.filter(company=self).order_by('id')

    def get_cfields_list(self, show_hidden=True):
        cfields = []
        for cf in CField.objects.filter(company=self).order_by('id'):

            if show_hidden:
                cfields.append(cf)
            else:
                cfa = CFieldAuto.objects.filter(company=self, cfield=cf).first()
                if not (cfa and cfa.hide):
                    cfields.append(cf)

        return cfields

    def get_eforms(self):
        return EventForm.objects.filter(company=self).order_by('id')

    def get_event_types(self):
        return EventType.objects.filter(company=self).order_by('id')

    def get_unknown_contact_company(self):
        now = timezone.localtime(timezone.now())
        # Create new contact company
        cc = ContactCompany(company=self,
                            name='unknown',
                            created=now,
                            updated=now)
        cc.save()
        return cc

    def get_unknown_contact_type(self):
        ct = ContactType.objects.filter(company=self, name__iexact='unknown').first()
        if ct is None:
            # Date : 23-10-2019
            # AIT - CAL -16 : WEB - PROJECT - Create new Contact Type "Internal Staff"
            # Desc : reference_contact_type_name name are added.
            ct = ContactType(company=self, name='unknown', reference_contact_type_name='unknown')
            ct.save()
        return ct

    def find_dupes(self):
        cursor = connection.cursor()
        out = ''
        np = re.compile('[^-a-zA-Z0-9\ _]')

        # clear existing duplicates
        sql = """
          DELETE FROM cp_duplicatecontact
          WHERE cp_duplicatecontact.company_id = %s
          AND never_merge = 'F'
        """ % self.id

        cursor.execute(sql)
        # Date : 07-August-2020
        # AIT - CPV1-161 : Find Duplicates Mechanism does not seem to work on PEOPLE accounts
        # Desc : This change is used to update the transaction library
        transaction.atomic()

        sql = """
          DELETE FROM cp_duplicatecontactcompany
          WHERE cp_duplicatecontactcompany.company_id = %s
          AND never_merge = 'F'
        """ % self.id

        cursor.execute(sql)
        # Date : 07-August-2020
        # AIT - CPV1-161 : Find Duplicates Mechanism does not seem to work on PEOPLE accounts
        # Desc : This change is used to update the transaction library
        transaction.atomic()

        # Date : 28-July-2020
        # AIT - CPV1-161 : WEB - PROJECT - Find Duplicates Mechanism does not seem to work on PEOPLE accounts
        # Desc : The below section is used to check the requested company have people tab or not
        if not self.people_tab:
            # blank contacts
            for contact in Contact.objects \
                    .filter(company=self) \
                    .filter(Q(first_name=None) |
                            Q(last_name=None) |
                            Q(first_name='') |
                            Q(last_name='')):
                dc = DuplicateContact.objects.filter(company=self, contact=contact).first()
                if dc:
                    # already found dupes for this contact
                    continue

                try:
                    cc = contact.contact_company
                except:
                    cc = None
                if cc is None:
                    continue

                try:
                    fn = contact.first_name
                except:
                    fn = None
                if fn is None:
                    continue

                try:
                    ln = contact.last_name
                except:
                    ln = None
                if ln is None:
                    continue

                duplicate_contacts = []
                for duplicate in Contact.objects.filter(company=self,
                                                        first_name__iexact=fn,
                                                        last_name__iexact=ln,
                                                        contact_company=cc).exclude(id=contact.id):
                    duplicate_contacts.append(DuplicateContact(company=self, contact=contact, duplicate=duplicate))

                if duplicate_contacts:
                    try:
                        DuplicateContact.objects.bulk_create(duplicate_contacts)
                    except:
                        pass

            # contacts
            for contact in Contact.objects \
                    .filter(company=self) \
                    .exclude(first_name=None) \
                    .exclude(last_name=None) \
                    .exclude(first_name='') \
                    .exclude(last_name=''):
                dc = DuplicateContact.objects.filter(company=self, contact=contact).first()
                if dc:
                    # already found dupes for this contact
                    continue

                duplicate_contacts = []
                for duplicate in Contact.objects \
                        .filter(company=self,
                                first_name__iexact=contact.first_name,
                                last_name__iexact=contact.last_name) \
                        .exclude(id=contact.id):
                    duplicate_contacts.append(DuplicateContact(company=self, contact=contact, duplicate=duplicate))

                if duplicate_contacts:
                    try:
                        DuplicateContact.objects.bulk_create(duplicate_contacts)
                    except:
                        pass

            # companies
            for contact_company in ContactCompany.objects.filter(company=self):
                dcc = DuplicateContactCompany.objects \
                    .filter(company=self, contact_company=contact_company).first()
                if dcc:
                    # already found dupes for this company
                    continue

                name = np.sub('', contact_company.name)

                sql = """
                SELECT cp_contactcompany.id AS id
                FROM cp_contactcompany
                WHERE cp_contactcompany.company_id = %s
                AND cp_contactcompany.id != %s
                AND soundex( cp_contactcompany.name ) = soundex( '%s' )
                AND levenshtein( cp_contactcompany.name, '%s', 1, 0, 4 ) < 2
                ORDER by levenshtein( cp_contactcompany.name, '%s', 1, 0, 4 )
                """ % (self.id, contact_company.id, name, name, name)

                duplicate_contact_companies = []
                for duplicate in list(ContactCompany.objects.raw(sql)):
                    dcc = DuplicateContactCompany(company=self,
                                                  contact_company=contact_company,
                                                  duplicate=duplicate)
                    duplicate_contact_companies.append(dcc)
                if duplicate_contact_companies:
                    try:
                        DuplicateContactCompany.objects.bulk_create(duplicate_contact_companies)
                    except:
                        pass
            return out

        # If the requested company have people tab below section will be executed
        else:
            # To find the duplicate contacts based on contact first_name and last_name
            for contact in Contact.objects \
                    .filter(company=self) \
                    .exclude(first_name=None) \
                    .exclude(last_name=None) \
                    .exclude(first_name='') \
                    .exclude(last_name=''):
                duplicate_contact = DuplicateContact.objects \
                    .filter(company=self, contact=contact).first()
                if duplicate_contact:
                    # Duplication already found for the contact
                    continue

                duplicate_contacts = []
                for duplicate in Contact.objects \
                        .filter(company=self,
                                first_name__iexact=contact.first_name,
                                last_name__iexact=contact.last_name) \
                        .exclude(id=contact.id):
                    duplicate_contacts.append(DuplicateContact(company=self,
                                                               contact=contact,
                                                               duplicate=duplicate))

                if duplicate_contacts:
                    try:
                        DuplicateContact.objects.bulk_create(duplicate_contacts)
                    except:
                        pass

            # To find the duplicate companies based on contact company name
            for contact_company in ContactCompany.objects.filter(company=self):
                duplicate_contact_company = DuplicateContactCompany.objects \
                    .filter(company=self,
                            contact_company=contact_company).first()
                if duplicate_contact_company:
                    # duplication already found for the contact
                    continue

                name = np.sub('', contact_company.name)
                sql = """
                SELECT cp_contactcompany.id AS id
                FROM cp_contactcompany
                WHERE cp_contactcompany.company_id = %s
                AND cp_contactcompany.id != %s
                AND soundex( cp_contactcompany.name ) = soundex( '%s' )
                AND levenshtein( cp_contactcompany.name, '%s', 1, 0, 4 ) < 2
                ORDER by levenshtein( cp_contactcompany.name, '%s', 1, 0, 4 )
                """ % (self.id, contact_company.id, name, name, name)
                
                duplicate_contact_companies = []
                for duplicate in list(ContactCompany.objects.raw(sql)):
                    duplicate_contact_companies.append(DuplicateContactCompany(company=self,
                                                                               contact_company=contact_company,
                                                                               duplicate=duplicate))

                if duplicate_contact_companies:
                    try:
                        DuplicateContactCompany.objects.bulk_create(duplicate_contact_companies)
                    except:
                        pass

            # To find the duplicate contacts based on contact phone number
            for contact_phone in ContactPhone.objects.filter(company=self):
                duplicate_contact = DuplicateContact.objects \
                    .filter(company=self,
                            contact=contact_phone.contact_id).first()

                if duplicate_contact:
                    # Duplication already found for the contact
                    continue

                duplicate_contacts = []
                for duplicate in ContactPhone.objects \
                        .filter(company=self,
                                phone_number=contact_phone.phone_number) \
                        .exclude(id=contact_phone.id):
                    duplicate_contacts.append(DuplicateContact(company=self,
                                                               contact=contact_phone.contact,
                                                               duplicate=duplicate.contact))
                if duplicate_contacts:
                    try:
                        DuplicateContact.objects.bulk_create(duplicate_contacts)
                    except:
                        pass

            # To find the duplicate contacts based on Street and City
            for contact in Contact.objects \
                    .filter(company=self) \
                    .exclude(address=None) \
                    .exclude(city=None) \
                    .exclude(address='') \
                    .exclude(city=''):
                duplicate_contact = DuplicateContact.objects \
                    .filter(company=self, contact=contact).first()

                if duplicate_contact:
                    # Duplication already found for the contact
                    continue

                duplicate_contacts = []
                for duplicate in Contact.objects \
                        .filter(company=self,
                                address__iexact=contact.address,
                                city__iexact=contact.city) \
                        .exclude(id=contact.id):
                    duplicate_contacts.append(DuplicateContact(company=self,
                                                               contact=contact,
                                                               duplicate=duplicate))
                if duplicate_contacts:
                    try:
                        DuplicateContact.objects.bulk_create(duplicate_contacts)
                    except:
                        pass

            # To find the duplicate contacts based on Street and Contact Company name
            for contact in Contact.objects \
                    .filter(company=self) \
                    .exclude(address=None) \
                    .exclude(address=''):
                duplicate_contact = DuplicateContact.objects.filter(company=self,
                                                                    contact=contact).first()

                if duplicate_contact:
                    # Duplication already found for the contact
                    continue

                duplicate_contacts = []
                for duplicate in Contact.objects \
                        .filter(company=self,
                                contact_company__name__iexact=contact.contact_company.name,
                                city__iexact=contact.city) \
                        .exclude(id=contact.id):
                    duplicate_contacts.append(DuplicateContact(company=self,
                                                               contact=contact,
                                                               duplicate=duplicate))

                if duplicate_contacts:
                    try:
                        DuplicateContact.objects.bulk_create(duplicate_contacts)
                    except:
                        pass
            return out

        return out

    def get_transaction_months(self):
        if self.transaction_months:
            return self.transaction_months
        return 18

    def get_call_buy_days(self):
        if self.call_buy_days:
            return self.call_buy_days
        return 14

    def emails_count_between(self, user_profiles, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = EmailMsg.objects.filter(sent_date__gte=dt, sent_date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.count()
        return s

    def calls_count_between(self, user_profiles, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatCallDaily.objects.filter(date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.aggregate(Sum('count'))['count__sum']
        if s is None:
            s = 0
        return s

    def calls_duration_between(self, user_profiles, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatCallDaily.objects.filter(date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def rec_calls_count_between(self, user_profiles, dt, dt2,
                                contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatTwilioCallDaily.objects.filter(date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=10),
            When(call_type_id__in=(3, 4), then=0))
        )
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.aggregate(Sum('count'))['count__sum']
        if s is None:
            s = 0
        return s

    def rec_calls_count_between_awr(self, user_profiles, dt, dt2,
                                    contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = TwilioCall.objects.filter(start__gte=dt, start__lt=dt2)
        if contact_type:
            s = s.filter(contact__contact_type=contact_type)
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=11),
            When(call_type_id__in=(3, 4), then=0))
        )
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        return s.count()

    def rec_calls_duration_between(self, user_profiles, dt, dt2,
                                   contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatTwilioCallDaily.objects.filter(date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=10),
            When(call_type_id__in=(3, 4), then=0))
        )
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def rec_calls_duration_between_awr(self, user_profiles, dt, dt2,
                                       contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = TwilioCall.objects.filter(start__gte=dt, start__lt=dt2)
        if contact_type:
            s = s.filter(contact__contact_type=contact_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=11),
            When(call_type_id__in=(3, 4), then=0))
        )
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def appts_count_between(self, user_profiles, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatApptDaily.objects.filter(date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.aggregate(Sum('count'))['count__sum']
        if s is None:
            s = 0
        return s

    def appts_duration_between(self, user_profiles, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatApptDaily.objects.filter(date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def followups_count_between(self, user_profiles, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatFollowupDaily.objects.filter(date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.aggregate(Sum('count'))['count__sum']
        if s is None:
            s = 0
        return s

    def followups_duration_between(self, user_profiles, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatFollowupDaily.objects.filter(date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        user_ids = [str(up.user_id) for up in user_profiles]
        if len(user_ids) == 0:
            user_ids = ['0']
        where = 'user_id IN (%s)' % ','.join(user_ids)
        s = s.extra(where=[where])
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def twilio_phone_numbers_count(self):
        return TwilioPhoneNumber.objects.filter(company=self).count()

    def twilio_phone_numbers(self):
        return TwilioPhoneNumber.objects.filter(company=self).order_by('-created')

    def get_dealer_stores(self):
        return DealerStore.objects.filter(company=self).order_by('name')

    def get_dealer_stores_with_phones(self):
        stores = []
        for ds in DealerStore.objects.filter(company=self).order_by('name'):
            dsp = DealerStorePhone.objects.filter(dealer_store=ds).first()
            if dsp:
                stores.append(ds)
        return stores

    def get_dealer_store_phone_ids(self, store_id=None):
        ids, stores = [], []

        if store_id:
            ds = DealerStore.objects.filter(company=self, id=store_id).first()
            if ds:
                stores.append(ds)
        else:
            for ds in DealerStore.objects.filter(company=self):
                stores.append(ds)

        for ds in stores:
            for dsp in DealerStorePhone.objects.filter(dealer_store=ds):
                ids.append(str(dsp.id))

        return ids

    def get_dealer_store_phones(self):
        ids = []
        for ds in self.get_dealer_stores():
            ids.append(str(ds.id))
        where = 'dealer_store_id IN (0)'
        if ids:
            where = 'dealer_store_id IN (%s)' % ','.join(ids)
        store_phones = []
        for sp in DealerStorePhone.objects.extra(where=[where]).order_by('phone_number'):
            cid = TwilioCallerID.objects.filter(dealer_store_phone=sp, validated=True).first()
            if cid:
                store_phones.append(sp)
        return store_phones

    def setup_dealer(self):
        cts = ['Activation', 'Research', 'Upgrade', 'Service']
        for n in cts:
            ct = ContactType.objects.filter(company=self, name__iexact=n).first()
            if ct is None:
                # Date : 23-10-2019
                # AIT - CAL -16 : WEB - PROJECT - Create new Contact Type "Internal Staff"
                # Desc : reference_contact_type_name name are added.
                ct = ContactType(company=self, name=n, reference_contact_type_name=n)
                ct.save()

    def referer_vars(self):
        company_setting = CompanySetting.objects.filter(company=self, name='referer_hash').first()
        if company_setting is None:
            return []

        referer = Referer.objects.filter(hash=company_setting.value).first()
        if referer is None:
            return []

        return RefererVar.objects.filter(referer=referer).order_by('name')

    def get_amount(self):
        count = self.get_last_month_user_count()
        rate = 40 if count >= 10 else 45
        amount = count * rate
        if amount < 200:
            amount = 200
        return amount

    def get_billing_desc(self):
        count = self.get_last_month_user_count()

        rate = 40 if count >= 10 else 45
        amount = count * rate

        min_msg = ''
        if amount < 200:
            min_msg = ' ($200 min)'
            amount = 200

        desc = '''Active lines last month: %s
Per line cost: $%s
Amount invoiced: $%s %s
        ''' % (count, rate, amount, min_msg)

        return desc

    def found_us(self):
        f = ''

        try:
            u = self.first_up().user
        except:
            u = None

        if u:
            fu = UserSetting.objects.filter(user=u, name='found_us')[:1]
            try:
                fu = fu[0].value
            except:
                fu = ''

            fuo = UserSetting.objects.filter(user=u, name='found_us_other')[:1]
            try:
                fuo = fuo[0].value
            except:
                fuo = ''

            if fu == 'other':
                f = 'other: %s' % fuo
            else:
                f = '%s' % fu
        return f

    def first_up(self):
        return UserProfile.objects.filter(company=self).order_by('id').first()

    def created_short(self):
        try:
            last = self.created.strftime('%Y-%m-%d')
        except:
            last = None
        return last

    def oldest_unpaid_invoice(self):
        return Invoice.objects.filter(company=self, paid=False).order_by('invoice_date').first()

    def get_balance(self):
        b = 0
        for i in Invoice.objects.filter(company=self):
            b += i.still_owe()
        return b

    def last_event(self):
        ids = self.user_ids()
        if len(ids) > 0:
            e = Event.objects \
                .extra(where=['user_id IN (%s)' % ','.join(ids)]) \
                .order_by('-created').first()
            if e:
                return e.created
        return self.created

    def last_activity_short(self):
        try:
            last = self.last_activity.strftime('%Y-%m-%d')
        except:
            last = None
        return last

    def get_last_month_user_count(self):
        month_ago = timezone.localtime(timezone.now()) - timedelta(days=30)
        return Event.objects \
            .filter(company=self, created__gte=month_ago) \
            .distinct('user_id') \
            .count()

    def get_last_90_user_count(self):
        ninety_days_ago = timezone.localtime(timezone.now()) - timedelta(days=90)
        return Event.objects \
            .filter(company=self, created__gte=ninety_days_ago) \
            .distinct('user_id') \
            .count()

    def auth_net_delete_card(self):
        auth_net_log('%s: auth_net_delete_card()' % timezone.localtime(timezone.now()))
        cs = CompanySetting.objects.filter(company=self,
                                           name='auth_net_profile_id').first()

        if cs:
            xml = '''<?xml version="1.0" encoding="utf-8"?>
<deleteCustomerProfileRequest xmlns="AnetApi/xml/v1/schema/AnetApiSchema.xsd">
  <merchantAuthentication>
    <name>%s</name>
    <transactionKey>%s</transactionKey>
  </merchantAuthentication>
  <refId>%s</refId>
  <customerProfileId>%s</customerProfileId>
</deleteCustomerProfileRequest>

            ''' % (settings.AUTH_NET_API_LOGIN,
                   settings.AUTH_NET_TRANS_KEY,
                   self.id,
                   cs.value)

            auth_net_log('request: %s' % xml)

            h = http.client.HTTPSConnection(settings.AUTH_NET_WS_DOMAIN)
            headers = {"Content-type": "text/xml", "Accept": "text/plain"}
            h.request('POST', settings.AUTH_NET_WS_PATH, xml, headers)
            r = h.getresponse()
            xml = r.read().strip().decode('utf-8')

            auth_net_log('response: %s' % xml)

            cs.delete()

            cs = CompanySetting.objects.filter(company=self,
                                               name='auth_net_payment_profile_id').first()

            if cs:
                cs.delete()

    def auth_net_get_profile(self):
        auth_net_log('%s: auth_net_get_profile()' % timezone.localtime(timezone.now()))

        selected = {}
        cs = CompanySetting.objects.filter(company=self, name='auth_net_profile_id').first()
        if cs:
            cs2 = CompanySetting.objects.filter(company=self,
                                                name='auth_net_payment_profile_id').first()
            if cs2:
                xml = '''<?xml version="1.0" encoding="utf-8"?>
<getCustomerPaymentProfileRequest xmlns="AnetApi/xml/v1/schema/AnetApiSchema.xsd">
  <merchantAuthentication>
    <name>%s</name>
    <transactionKey>%s</transactionKey>
  </merchantAuthentication>
  <customerProfileId>%s</customerProfileId>
  <customerPaymentProfileId>%s</customerPaymentProfileId>
</getCustomerPaymentProfileRequest>
                ''' % (settings.AUTH_NET_API_LOGIN,
                       settings.AUTH_NET_TRANS_KEY,
                       cs.value,
                       cs2.value)

                auth_net_log('request: %s' % xml)

                h = http.client.HTTPSConnection(settings.AUTH_NET_WS_DOMAIN)
                headers = {"Content-type": "text/xml", "Accept": "text/plain"}
                h.request('POST', settings.AUTH_NET_WS_PATH, xml, headers)
                r = h.getresponse()
                xml = r.read().strip().decode('utf-8')

                auth_net_log('response: %s' % xml)

                err_p = re.compile('.*<resultCode>(.*)</resultCode>.*')
                err_m = err_p.match(xml)

                try:
                    error = err_m.group(1)
                except:
                    error = None

                if error and error == 'Error':
                    cs.delete()
                    cs2.delete()

                fn_p = re.compile('.*<firstName>(.*)</firstName>.*')
                ln_p = re.compile('.*<lastName>(.*)</lastName>.*')
                a_p = re.compile('.*<address>(.*)</address>.*')
                c_p = re.compile('.*<city>(.*)</city>.*')
                s_p = re.compile('.*<state>(.*)</state>.*')
                z_p = re.compile('.*<zip>(.*)</zip>.*')
                cc_p = re.compile('.*<country>(.*)</country>.*')
                pn_p = re.compile('.*<phoneNumber>(.*)</phoneNumber>.*')
                lf_p = re.compile('.*<cardNumber>(.*)</cardNumber>.*')

                fn_m = fn_p.match(xml)
                ln_m = ln_p.match(xml)
                a_m = a_p.match(xml)
                c_m = c_p.match(xml)
                s_m = s_p.match(xml)
                z_m = z_p.match(xml)
                cc_m = cc_p.match(xml)
                pn_m = pn_p.match(xml)
                lf_m = lf_p.match(xml)

                try:
                    selected['card_number'] = lf_m.group(1)
                except:
                    selected['card_number'] = ''

                try:
                    selected['last_four'] = '************%s' % lf_m.group(1)[4:8]
                except:
                    selected['last_four'] = ''

                try:
                    selected['first_name'] = fn_m.group(1)
                except:
                    selected['first_name'] = ''

                try:
                    selected['last_name'] = ln_m.group(1)
                except:
                    selected['last_name'] = ''

                try:
                    selected['phone'] = pn_m.group(1)
                except:
                    selected['phone'] = ''

                try:
                    selected['address'] = a_m.group(1)
                except:
                    selected['address'] = ''

                try:
                    selected['city'] = c_m.group(1)
                except:
                    selected['city'] = ''

                try:
                    selected['zip'] = z_m.group(1)
                except:
                    selected['zip'] = ''

                try:
                    s = State.objects.filter(name=s_m.group(1))[:1]
                    s = s[0]
                except:
                    s = None

                if s:
                    selected['state_id'] = s.id
                else:
                    selected['state_id'] = ''

                try:
                    c = Country.objects.filter(name=cc_m.group(1))[:1]
                    c = c[0]
                except:
                    c = None
                if c:
                    selected['country_id'] = c.id
                else:
                    selected['country_id'] = ''

        return selected

    def auth_net_create_profile(self, user):
        auth_net_log('%s: auth_net_create_profile()' % timezone.localtime(timezone.now()))

        xml = '''<?xml version="1.0" encoding="utf-8"?>
<createCustomerProfileRequest xmlns="AnetApi/xml/v1/schema/AnetApiSchema.xsd">
  <merchantAuthentication>
    <name>%s</name>
    <transactionKey>%s</transactionKey>
  </merchantAuthentication>
  <refId>%s</refId>
  <profile>
    <merchantCustomerId>%s</merchantCustomerId>
    <description>%s</description>
    <email>%s</email>
  </profile>
</createCustomerProfileRequest>

        ''' % (settings.AUTH_NET_API_LOGIN,
               settings.AUTH_NET_TRANS_KEY,
               self.id,
               user.id,
               escape(self.name),
               user.email)

        auth_net_log('request: %s' % xml)

        h = http.client.HTTPSConnection(settings.AUTH_NET_WS_DOMAIN)
        headers = {"Content-type": "text/xml", "Accept": "text/plain"}
        h.request('POST', settings.AUTH_NET_WS_PATH, xml, headers)
        r = h.getresponse()
        xml = r.read().strip().decode('utf-8')

        auth_net_log('response: %s' % xml)

        c_p = re.compile('.*<customerProfileId>(\d+)</customerProfileId>.*', re.S)
        d_p = re.compile('.*<code>E00039</code>.*', re.S)
        did_p = re.compile('.*<text>A duplicate record with ID (\d+) already exists.</text>.*')

        c_m = c_p.match(xml)
        d_m = d_p.match(xml)
        did_m = did_p.match(xml)

        try:
            auth_net_profile_id = int(c_m.group(1))
        except:
            auth_net_profile_id = 0

        if auth_net_profile_id == 0:
            try:
                auth_net_profile_id = int(did_m.group(1))
            except:
                auth_net_profile_id = 0

        auth_net_log('auth_net_profile_id: %s' % auth_net_profile_id)

        if auth_net_profile_id > 0:
            cs = CompanySetting.objects.filter(company=self, name='auth_net_profile_id').first()
            now = timezone.localtime(timezone.now())
            if cs:
                cs.value = auth_net_profile_id
                cs.updated = now
            else:
                cs = CompanySetting(company=self,
                                    name='auth_net_profile_id',
                                    value=auth_net_profile_id,
                                    updated=now)
            cs.save()

        return auth_net_profile_id

    def auth_net_update_profile(self, auth_net_profile_id, user):
        auth_net_log('%s: auth_net_update_profile()' % timezone.localtime(timezone.now()))

        xml = '''<?xml version="1.0" encoding="utf-8"?>
<updateCustomerProfileRequest xmlns="AnetApi/xml/v1/schema/AnetApiSchema.xsd">
  <merchantAuthentication>
    <name>%s</name>
    <transactionKey>%s</transactionKey>
  </merchantAuthentication>
  <refId>%s</refId>
  <profile>
    <merchantCustomerId>%s</merchantCustomerId>
    <description>%s</description>
    <email>%s</email>
    <customerProfileId>%s</customerProfileId>
  </profile>
</updateCustomerProfileRequest>

        ''' % (settings.AUTH_NET_API_LOGIN,
               settings.AUTH_NET_TRANS_KEY,
               self.id,
               user.id,
               escape(self.name),
               user.email,
               auth_net_profile_id)

        auth_net_log('request: %s' % xml)

        h = http.client.HTTPSConnection(settings.AUTH_NET_WS_DOMAIN)
        headers = {"Content-type": "text/xml", "Accept": "text/plain"}
        h.request('POST', settings.AUTH_NET_WS_PATH, xml, headers)
        r = h.getresponse()
        xml = r.read().strip().decode('utf-8')

        auth_net_log('response: %s' % xml)

        c_p = re.compile('.*<customerProfileId>(\d+)</customerProfileId>.*', re.S)
        c_m = c_p.match(xml)

        try:
            auth_net_profile_id = int(c_m.group(1))
        except:
            auth_net_profile_id = 0

        auth_net_log('auth_net_profile_id: %s' % auth_net_profile_id)

        if auth_net_profile_id > 0:
            cs = CompanySetting.objects.filter(company=self, name='auth_net_profile_id').first()
            now = timezone.localtime(timezone.now())

            if cs:
                cs.value = auth_net_profile_id
                cs.updated = now
            else:
                cs = CompanySetting(company=self,
                                    name='auth_net_profile_id',
                                    value=auth_net_profile_id,
                                    updated=now)
            cs.save()

        return auth_net_profile_id

    def auth_net_create_payment_profile(self, auth_net_profile_id, selected):
        auth_net_log('%s: auth_net_create_payment_profile()' % timezone.localtime(timezone.now()))

        xml = '''<?xml version="1.0" encoding="utf-8"?>
<createCustomerPaymentProfileRequest xmlns="AnetApi/xml/v1/schema/AnetApiSchema.xsd">
  <merchantAuthentication>
    <name>%s</name>
    <transactionKey>%s</transactionKey>
  </merchantAuthentication>
  <refId>%s</refId>
  <customerProfileId>%s</customerProfileId>
  <paymentProfile>
    <billTo>
      <firstName>%s</firstName>
      <lastName>%s</lastName>
      <company>%s</company>
      <address>%s</address>
      <city>%s</city>
      <state>%s</state>
      <zip>%s</zip>
      <country>%s</country>
      <phoneNumber>%s</phoneNumber>
    </billTo>
    <payment>
      <creditCard>
        <cardNumber>%s</cardNumber>
        <expirationDate>%s</expirationDate>
        <cardCode>%s</cardCode>
      </creditCard>
    </payment>
  </paymentProfile>
</createCustomerPaymentProfileRequest>
        ''' % (settings.AUTH_NET_API_LOGIN,
               settings.AUTH_NET_TRANS_KEY,
               self.id,
               auth_net_profile_id,
               escape(selected['first_name']),
               escape(selected['last_name']),
               escape(self.name),
               escape(selected['address']),
               escape(selected['city']),
               escape(selected['state'].name),
               selected['zip'],
               escape(selected['country'].name),
               selected['phone'],
               selected['card_number'],
               selected['expires'],
               selected['code'])

        auth_net_log('request: %s' % xml)

        h = http.client.HTTPSConnection(settings.AUTH_NET_WS_DOMAIN)
        headers = {"Content-type": "text/xml", "Accept": "text/plain"}
        h.request('POST', settings.AUTH_NET_WS_PATH, xml, headers)
        r = h.getresponse()
        xml = r.read().strip().decode('utf-8')

        auth_net_log('response: %s' % xml)

        c_p = re.compile('.*<customerPaymentProfileId>(\d+)</customerPaymentProfileId>.*', re.S)

        c_m = c_p.match(xml)

        try:
            auth_net_payment_profile_id = int(c_m.group(1))
        except:
            auth_net_payment_profile_id = 0

        auth_net_log('auth_net_payment_profile_id: %s' % auth_net_payment_profile_id)

        if auth_net_payment_profile_id > 0:
            cs = CompanySetting.objects.filter(company=self,
                                               name='auth_net_payment_profile_id').first()
            now = timezone.localtime(timezone.now())
            if cs:
                cs.value = auth_net_payment_profile_id
                cs.updated = now
            else:
                cs = CompanySetting(company=self,
                                    name='auth_net_payment_profile_id',
                                    value=auth_net_payment_profile_id,
                                    updated=now)
            cs.save()

        return auth_net_payment_profile_id

    def auth_net_update_payment_profile(self, auth_net_profile_id,
                                        auth_net_payment_profile_id, selected):
        auth_net_log('%s: auth_net_update_payment_profile()' % timezone.localtime(timezone.now()))

        xml = '''<?xml version="1.0" encoding="utf-8"?>
<updateCustomerPaymentProfileRequest xmlns="AnetApi/xml/v1/schema/AnetApiSchema.xsd">
  <merchantAuthentication>
    <name>%s</name>
    <transactionKey>%s</transactionKey>
  </merchantAuthentication>
  <refId>%s</refId>
  <customerProfileId>%s</customerProfileId>
  <paymentProfile>
    <billTo>
      <firstName>%s</firstName>
      <lastName>%s</lastName>
      <company>%s</company>
      <address>%s</address>
      <city>%s</city>
      <state>%s</state>
      <zip>%s</zip>
      <country>%s</country>
      <phoneNumber>%s</phoneNumber>
    </billTo>
    <payment>
      <creditCard>
        <cardNumber>%s</cardNumber>
        <expirationDate>%s</expirationDate>
        <cardCode>%s</cardCode>
      </creditCard>
    </payment>
    <customerPaymentProfileId>%s</customerPaymentProfileId>
  </paymentProfile>
</updateCustomerPaymentProfileRequest>
        ''' % (settings.AUTH_NET_API_LOGIN,
               settings.AUTH_NET_TRANS_KEY,
               self.id,
               auth_net_profile_id,
               escape(selected['first_name']),
               escape(selected['last_name']),
               escape(self.name),
               escape(selected['address']),
               escape(selected['city']),
               escape(selected['state'].name),
               selected['zip'],
               escape(selected['country'].name),
               selected['phone'],
               selected['card_number'],
               selected['expires'],
               selected['code'],
               auth_net_payment_profile_id)

        auth_net_log('request: %s' % xml)

        h = http.client.HTTPSConnection(settings.AUTH_NET_WS_DOMAIN)
        headers = {"Content-type": "text/xml", "Accept": "text/plain"}
        h.request('POST', settings.AUTH_NET_WS_PATH, xml, headers)
        r = h.getresponse()
        xml = r.read().strip().decode('utf-8')

        auth_net_log('response: %s' % xml)

        c_p = re.compile('.*<customerPaymentProfileId>(\d+)</customerPaymentProfileId>.*', re.S)
        c_m = c_p.match(xml)

        try:
            auth_net_payment_profile_id = int(c_m.group(1))
        except:
            auth_net_payment_profile_id = 0

        auth_net_log('auth_net_payment_profile_id: %s' % auth_net_payment_profile_id)

        if auth_net_payment_profile_id > 0:
            cs = CompanySetting.objects.filter(company=self,
                                               name='auth_net_payment_profile_id').first()
            now = timezone.localtime(timezone.now())

            if cs:
                cs.value = auth_net_payment_profile_id
                cs.updated = now
            else:
                cs = CompanySetting(company=self,
                                    name='auth_net_payment_profile_id',
                                    value=auth_net_payment_profile_id,
                                    updated=now)
            cs.save()

        return auth_net_payment_profile_id

    def get_expired_status(self):
        t = timezone.localtime(timezone.now()) - timedelta(days=30)
        if self.created < t:
            return 'expired'

        l = timezone.localtime(timezone.now()) - self.created

        if l.days > 0:
            return '%s more days' % l.days
        return ''

    def membership(self):
        return Membership.objects.filter(company=self).first()

    def current_billing_opt(self):
        membership = Membership.objects.filter(company=self).first()
        if membership:
            return membership.billing_opt

    def current_plan(self):
        membership = Membership.objects.filter(company=self).first()
        if membership:
            return membership.plan

    def get_opps_list(self):
        return Opp.objects.filter(company=self).order_by('id')

    def get_opps(self, funnel_user_id=None, start=None, stop=None,
                 start_funnel_probability=0, end_funnel_probability=0,
                 funnel_market_ids=None, **kwargs):
        opps = []
        opps_list = Opp.objects.filter(company=self)
        request = kwargs.get('request')
        if request and request.user_profile.just_my_events:
            opps_list = opps_list.filter(user=request.user)

        # CPV1-2495 Opportunity report with contact type filter
        if request is not None and request.session.get('contact_type', []):
            opps_list = opps_list.filter(contact__contact_type_id__in=request.session.get('contact_type'))
        if len(funnel_user_id) > 0:
            opps_list = opps_list.filter(user__in=funnel_user_id)
        elif funnel_market_ids:
            opps_list = {}
            return opps_list

        if request:
            date_filter = request.session.get('funnel_date_filter') or 'close'
        else:
            date_filter = 'close'

        if start:
            if date_filter == 'created':
                opps_list = opps_list.filter(created__gte=start)
            else:
                opps_list = opps_list.filter(close_date__gte=start)
        if stop:
            if date_filter == 'created':
                opps_list = opps_list.filter(created__lt=stop + timedelta(days=1))
            else:
                opps_list = opps_list.filter(close_date__lt=stop + timedelta(days=1))

        # To filter the opportunities or funnel based on the start and end value probability
        if start_funnel_probability and start_funnel_probability.isdigit():
            opps_list = opps_list.filter(probability__gte=start_funnel_probability)
        if end_funnel_probability and end_funnel_probability.isdigit():
            opps_list = opps_list.filter(probability__lte=end_funnel_probability)

        opps_list = opps_list.order_by('close_date')
        for o in opps_list:
            opp = {}
            opp['obj'] = o
            opp['id'] = o.id
            opp['user'] = o.user
            opp['contact'] = o.contact
            opp['create_date'] = o.created
            try:
                opp['opptype'] = o.opp_type
            except:
                opp['opptype'] = None

            try:
                opp['oppstage'] = o.opp_stage
            except:
                opp['oppstage'] = None
            try:
                opp['opp_name'] = o.opp_name if o.opp_name else ''
            except:
                opp['opp_name'] = ''

            opp['probability'] = o.probability
            opp['value'] = o.value
            opp['derived'] = o.value * o.probability / 100
            opp['close_date'] = o.close_date.strftime('%b %d, %Y')
            opp['cl_date'] = o.close_date
            opp['updated'] = o.updated
            notes = []
            opp_history = OppHistory.objects.filter(opp=o,
                                                    close_date__gte=start,
                                                    close_date__lt=stop).order_by('-id')

            # To filter the opportunity history based on the start and end value probability
            if start_funnel_probability and start_funnel_probability.isdigit():
                opp_history = opp_history.filter(probability__gte=start_funnel_probability)
            if end_funnel_probability and end_funnel_probability.isdigit():
                opp_history = opp_history.filter(probability__lte=end_funnel_probability)

            for history in opp_history:
                try:
                    the_note = history.notes.strip().replace('\n', ' ').replace('\r', ' ')
                except:
                    the_note = ''
                created = history.created.strftime('%b %d, %Y')
                notes.append('%s - %s' % (created, the_note))

            opp['notes'] = ' '.join(notes)
            opps.append(opp)
        return opps

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))

    def next_opptype_position(self):
        ot = OppType.objects.filter(company=self).order_by('-position').first()
        if ot:
            return ot.position + 1
        return 0

    def next_followuptype_position(self):
        ft = FollowupType.objects.filter(company=self).order_by('-position').first()
        if ft:
            return ft.position + 1
        return 0

    def next_oppstage_position(self):
        os = OppStage.objects.filter(company=self).order_by('-position').first()
        if os:
            return os.position + 1
        return 0

    def next_followup_stage_position(self):
        followup_stages = FollowupStage.objects.filter(company=self)\
                                               .order_by('-position')\
                                               .first()
        if followup_stages:
            return followup_stages.position + constants.INCREMENT_COUNT
        return constants.COUNT_ZERO

    def get_custom_fields(self, table=None, show_hidden=True):
        cfield_table = CFieldTable.objects.filter(name=table)[:1][0]
        cfields = []
        for cf in CField.objects.filter(company=self,
                                        cfield_table=cfield_table).order_by('position'):
            if show_hidden:
                cfields.append(cf)
            else:
                cfa = CFieldAuto.objects.filter(company=self, cfield=cf).first()
                if not (cfa and cfa.hide):
                    cfields.append(cf)

        custom_fields = []
        for x in range(0, len(cfields), 2):
            cfs1 = cfields[x]
            try:
                cfs2 = cfields[x + 1]
            except:
                cfs2 = None
            custom_fields.append([cfs1, cfs2])
        return custom_fields

    def get_custom_fields_list(self, table=None, show_hidden=True, show_img_fields=True):
        image = CFieldType.objects.filter(name='image')[:1][0]
        cfield_table = CFieldTable.objects.filter(name=table)[:1][0]
        cfields = []
        for cf in CField.objects.filter(company=self,
                                        cfield_table=cfield_table).order_by('position'):
            if show_hidden:
                if cf.cfield_type == image:
                    if show_img_fields:
                        cfields.append(cf)
                else:
                    cfields.append(cf)
            else:
                cfa = CFieldAuto.objects.filter(company=self, cfield=cf).first()
                if not (cfa and cfa.hide):
                    if cf.cfield_type == image:
                        if show_img_fields:
                            cfields.append(cf)
                    else:
                        cfields.append(cf)

        return cfields

    def next_cfield_option_position(self, cfield):
        if cfield is None:
            return 0
        cfield_option = CFieldOption.objects.filter(cfield=cfield).order_by('-position').first()
        return cfield_option.position + 1 if cfield_option else 0

    def next_cfield_position(self, cfield_table):
        if cfield_table is None:
            return 0
        cfield = CField.objects.filter(company=self,
                                       cfield_table=cfield_table).order_by('-position').first()
        return cfield.position + 1 if cfield else 0

    def unassigned_leads(self):
        contacts = []
        for c in Contact.objects.filter(company=self):
            cr = ContactRep.objects.filter(contact=c, contact__company=c.company)
            try:
                cr = cr[0]
            except:
                cr = None
            if cr is None:
                contacts.append(c)
        return contacts

    def eligible_contact_phone_ids(self):
        # 2021-02-23: MT: It appears that this might not be used anywhere.
        cp_ids = []
        contact_ids = self.contact_ids()
        if len(contact_ids) == 0:
            contact_ids = ['0']
        where = 'contact_id IN (%s)' % ','.join(contact_ids)
        for cp in ContactPhone.objects \
                .extra(where=[where]) \
                .exclude(Q(eligible__isnull=True)) \
                .filter(eligible__lte=timezone.localtime(timezone.now())):
            cp_ids.append(str(cp.id))
        return cp_ids

    def contact_phone_ids(self):
        # 2021-02-23: MT: It appears that this might not be used anywhere.
        cp_ids = []
        contact_ids = self.contact_ids()
        if len(contact_ids) == 0:
            contact_ids = ['0']
        where = 'contact_id IN (%s)' % ','.join(contact_ids)
        for cp in ContactPhone.objects.extra(where=[where]):
            cp_ids.append(str(cp.id))
        return cp_ids

    def contact_ids(self):
        # 2021-02-23: MT: This query seems to be used in areas where it result in
        # extremely sub-optimal queries. It appears that some of those areas could be
        # eliminated and thus, this function could be eliminated as well.
        contact_id_ints = list(Contact.objects.values_list('id', flat=True).filter(company=self))
        contact_id_strings = [str(contact_id) for contact_id in contact_id_ints]
        return contact_id_strings

    def contacts_count(self):
        return Contact.objects.filter(company=self).count()

    def events_count(self):
        return Event.objects.filter(company=self).count()

    def calls_count(self):
        return Call.objects.filter(company=self).count()

    def appointments_count(self):
        return Appointment.objects.filter(company=self).count()

    def followups_count(self):
        ids = self.user_ids()
        if len(ids) > 0:
            where = 'user_id IN (%s)' % ','.join(ids)
            return Followup.objects.extra(where=[where]).aggregate(Count('id'))['id__count']
        return 0

    def emails_count(self):
        return Email.objects.filter(company=self).count()

    def google_contacts_count(self):
        ids = self.user_ids()
        if len(ids) > 0:
            where = 'user_id IN (%s)' % ','.join(ids)
            return GoogleContact.objects.extra(where=[where]).aggregate(Count('id'))['id__count']
        return 0

    def get_users(self):
        return list(
            User.objects.filter(userprofile__company=self)
                .order_by('first_name', 'last_name'))

    def get_active_users(self):
        return list(
            User.objects.filter(userprofile__company=self)
                .exclude(usersetting__name='account_disabled')
                .order_by('first_name', 'last_name'))

    def get_managers(self):
        return list(
            UserProfile.objects
                .filter(company=self, manager=True)
                .exclude(user__usersetting__name='account_disabled')
                .order_by('user__first_name'))

    def get_non_managers(self):
        return list(
            UserProfile.objects
                .filter(company=self, manager=False)
                .exclude(user__usersetting__name='account_disabled')
                .order_by('user__first_name'))

    def get_non_company_active_users(self):
        return list(
            UserProfile.objects
                .filter(company=self, is_disabled=True, user__usersetting__name='account_disabled')
                .order_by('user__first_name'))

    def get_first_manager(self):
        user_profile = UserProfile.objects \
            .filter(company=self, manager=True) \
            .order_by('id') \
            .first()

        if user_profile:
            return user_profile.user
        return None

    def active_user_count(self):
        return UserProfile.objects \
            .values_list(str('user_id'), flat=True) \
            .filter(company=self) \
            .exclude(user__usersetting__name='account_disabled') \
            .count()

    def active_user_ids(self):
        return list(UserProfile.objects
                    .values_list(str('user_id'), flat=True)
                    .filter(company=self)
                    .exclude(user__usersetting__name='account_disabled'))

    def user_ids(self):
        user_id_ints = list(UserProfile.objects
                            .values_list('user_id', flat=True)
                            .filter(company=self))
        user_id_strings = [str(user_id) for user_id in user_id_ints]
        return user_id_strings

    def store_ids(self):
        store_ids = []
        for s in DealerStore.objects.filter(company=self):
            store_ids.append(str(s.id))
        return store_ids

    def appointments_today(self):
        try:
            count = Appointment.objects.extra(where=['user_id IN (%s)' % ','.join(self.user_ids())]).filter(
                start__gt=timezone.localtime(timezone.now()).replace(hour=0, minute=0, second=0,
                                                                     microsecond=0)).aggregate(Count('id'))['id__count']
        except:
            count = 0
        return count

    def appointments_week(self):
        try:
            count = Appointment.objects.extra(where=['user_id IN (%s)' % ','.join(self.user_ids())]).filter(start__gt=(
                    timezone.localtime(timezone.now()).replace(hour=0, minute=0, second=0,
                                                               microsecond=0) - timedelta(days=7))).aggregate(
                Count('id'))['id__count']
        except:
            count = 0
        return count

    def appointments_month(self):
        try:
            count = Appointment.objects.extra(where=['user_id IN (%s)' % ','.join(self.user_ids())]).filter(start__gt=(
                    timezone.localtime(timezone.now()).replace(hour=0, minute=0, second=0,
                                                               microsecond=0) - timedelta(days=30))).aggregate(
                Count('id'))['id__count']
        except:
            count = 0
        return count

    def calls_today(self):
        t = timezone.localtime(timezone.now()).replace(hour=0, minute=0, second=0, microsecond=0)
        where = 'user_id IN (%s)' % ','.join(self.user_ids())
        try:
            count = Call.objects.extra(where=[where]).filter(start__gt=t).aggregate(Count('id'))['id__count']
        except:
            count = 0

        try:
            count2 = TwilioCall.objects.filter(company=self, start__gt=t).aggregate(Count('id'))['id__count']
        except:
            count2 = 0

        return count + count2

    def calls_week(self):
        t = timezone.localtime(timezone.now()).replace(hour=0, minute=0, second=0, microsecond=0) - timedelta(days=7)
        where = 'user_id IN (%s)' % ','.join(self.user_ids())
        try:
            count = Call.objects.extra(where=[where]).filter(start__gt=t).aggregate(Count('id'))['id__count']
        except:
            count = 0
        return count

    def calls_month(self):
        t = timezone.localtime(timezone.now()).replace(hour=0, minute=0, second=0, microsecond=0) - timedelta(days=30)
        where = 'user_id IN (%s)' % ','.join(self.user_ids())
        try:
            count = Call.objects.extra(where=[where]).filter(start__gt=t).aggregate(Count('id'))['id__count']
        except:
            count = 0
        return count

    def get_places_category_list(self):
        cat_li = PlacesCategoryList.objects.filter(company=self).order_by('id')
        return list(cat_li)

    def get_prefill_opportunity_setting(self):
        """Get the company Opportunity prefill custom filed setting Enable or Disable"""
        company_setting = CompanySetting.objects.filter(name='prefill_opportunity_custom_field',
                                                        company=self).first()
        return True if company_setting and company_setting.value == '1' else False

    def get_assign_sales_rep(self):
        """Get the company default assign sales rep setting Enable or Disable"""
        company_setting = CompanySetting.objects.filter(name='default_assign_sales_rep',
                                                        company=self).first()
        return True if company_setting and company_setting.value == '1' else False


    class Meta:
        verbose_name_plural = 'companies'


class Badge(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=32)
    points = models.IntegerField()
    image = ImageField(upload_to=badge_image_path, null=True, blank=True)

    def __str__(self):
        return '%s' % self.name

    @staticmethod
    def badges():
        return {'Copper': 100,
                'Brass': 500,
                'Bronze': 2500,
                'Silver': 10000,
                'Palladium': 50000,
                'Gold': 250000,
                'Platinum': 1000000}


class Point(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=32)
    value = models.IntegerField()
    image = ImageField(upload_to=point_image_path, null=True, blank=True)

    def __str__(self):
        return '%s %s' % (self.name, self.value)

    def image_name(self):
        return '%s' % self.name.lower().replace(' ', '_')

    @staticmethod
    def points():
        return {'Oops': 0,
                'One Point': 1,
                'Two Points': 2,
                'Three Points': 3,
                'Four Points': 4,
                'Five Points': 5,
                'Ten Points': 10}


class EventType(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=32)
    desc = models.CharField(max_length=128)
    image = ImageField(upload_to=event_type_image_path, null=True, blank=True, max_length=255)
    updated = models.DateTimeField()

    def __str__(self):
        return self.proper_name()

    def proper_name(self):
        return '%s' % self.name.replace('_', ' ').title()

    def get_event_type_points(self):
        return self.eventtypepoint_set.all()

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))

    @staticmethod
    def sales_hustle_event():
        return ['hustle login', 'hustle place call', 'hustle start appt', 'hustle add followup']

    @staticmethod
    def types():
        twilio_log("function event type adding")
        return {'mobile_add_contact': 'added a new contact (mobile)',
                'mobile_add_contact_note': 'added a contact note (mobile)',
                'mobile_update_contact': 'updated a contact (mobile)',
                'web_add_contact': 'added a new contact (web)',
                'web_add_contact_note': 'added a contact note (web)',
                'web_update_contact': 'updated a contact (web)',
                'call_incoming': 'had an incoming call',
                'call_outgoing': 'had an outgoing call',
                'call_missed': 'missed an incoming call',
                'employee_call_incoming': 'had an incoming employee call',
                'employee_call_outgoing': 'had an outgoing employee call',
                'employee_call_missed': 'missed an incoming employee call',
                'contact_call_incoming': 'had an incoming contact call',
                'contact_call_outgoing': 'had an outgoing contact call',
                'contact_call_missed': 'missed an incoming contact call',
                'place_call_incoming': 'had an incoming place call',
                'place_call_outgoing': 'had an outgoing place call',
                'place_call_missed': 'missed an incoming place call',
                'mobile_appointment_checkin': 'checked into an appointment (mobile)',
                'mobile_appointment_checkout': 'checked out of an appointment (mobile)',
                'web_appointment_checkin': 'checked into an appointment (web)',
                'web_appointment_checkout': 'checked out of an appointment (web)',
                'mobile_clockin': 'clocked in (mobile)',
                'mobile_clockout': 'clocked out (mobile)',
                'web_clockin': 'clocked in (web)',
                'web_clockout': 'clocked out (web)',
                'mobile_login': 'logged in (mobile)',
                'mobile_logout': 'logged out (mobile)',
                'web_login': 'logged in (web)',
                'web_logout': 'logged out (web)',
                'badge_earned': 'earned a badge',

                'recorded_call': 'recorded a call',
                'recorded_call_1_star': 'had a call rated 1 star',
                'recorded_call_2_stars': 'had a call rated 2 stars',
                'recorded_call_3_stars': 'had a call rated 3 stars',
                'recorded_call_4_stars': 'had a call rated 4 stars',
                'recorded_call_5_stars': 'had a call rated 5 stars',

                'browser_call': 'recorded a browser call',
                'browser_call_1_star': 'had a call rated 1 star',
                'browser_call_2_stars': 'had a call rated 2 stars',
                'browser_call_3_stars': 'had a call rated 3 stars',
                'browser_call_4_stars': 'had a call rated 4 stars',
                'browser_call_5_stars': 'had a call rated 5 stars',

                'incoming_call': 'recorded a incoming call',
                'incoming_call_1_star': 'had a call rated 1 star',
                'incoming_call_2_stars': 'had a call rated 2 stars',
                'incoming_call_3_stars': 'had a call rated 3 stars',
                'incoming_call_4_stars': 'had a call rated 4 stars',
                'incoming_call_5_stars': 'had a call rated 5 stars',

                'event_form': 'saved an event form',

                'emailed': 'emailed',
                'received_email': 'received an email from',
                'outgoing_videomessage': 'has sent an video message',
                'get_team_status': 'get team status',

                }


class EventTypePoint(models.Model):
    event_type = models.ForeignKey(EventType, on_delete=models.CASCADE)
    point = models.ForeignKey(Point, on_delete=models.CASCADE)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s %s' % (self.event_type.name, self.point.__str__())


class MyCharField(models.CharField):
    def __init__(self, *args, **kwargs):
        super(MyCharField, self).__init__(*args, **kwargs)
        self.widget = TextInput(attrs={'class': 'text'})


class PhoneType(models.Model):
    name = models.CharField(max_length=32)
    position = models.IntegerField(default=0)

    def __str__(self):
        return '%s' % self.name

    def initial(self):
        return '%s' % self.name[0:1]


class UsernameField(CharField):

    def clean(self, value):
        super(UsernameField, self).clean(value)
        try:
            User.objects.get(username=value)
            raise ValidationError('Username already exists')
        except User.DoesNotExist:
            return value


class UserPhone(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    phone_type = models.ForeignKey(PhoneType, on_delete=models.CASCADE)
    phone_number = models.CharField(max_length=10, validators=[MinLengthValidator(10)])
    ext = models.CharField(max_length=4, blank=True)
    country_code = models.CharField(max_length=4)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s %s %s' % (self.user.first_name, self.user.last_name, self.phone_number)

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))

    def can_spoof(self):
        tcid = TwilioCallerID.objects.filter(user_phone=self).first()
        if tcid and tcid.status == 'Success' or tcid and tcid.status == 'success':
            return True
        return False


class Title(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    image = ImageField(upload_to=title_image_path, null=True, blank=True)
    contactmenulist = models.ForeignKey('ContactMenuList', null=True, blank=True, on_delete=models.SET_NULL)
    places_cat_list = models.ForeignKey(PlacesCategoryList, null=True, blank=True, on_delete=models.SET_NULL)

    def __str__(self):
        return '%s' % self.name

    @staticmethod
    def titles():
        return ['Sales', 'Owner', 'Rep', 'Other']


class Market(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=255)
    deleted = models.BooleanField(default=False)

    def __str__(self):
        return '%s' % self.name

    def stores(self):
        return self.marketstore_set.all().values_list('store_id', flat=True)


class Lookup(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_phone_id = models.TextField(null=True, blank=True)
    state = models.CharField(null=True, blank=True, max_length=50)
    created = models.DateTimeField()


class ContactMenuList(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=65)
    is_active = models.BooleanField(default=True)


class TaskNotificationMinuteChoice(models.Model):
    name = models.CharField(max_length=20)
    value = models.IntegerField()


class UserProfile(models.Model):
    user = models.OneToOneField(User, on_delete=models.CASCADE)
    store = models.ForeignKey('DealerStore', on_delete=models.SET_NULL, null=True, blank=True)
    limit_to_market = models.BooleanField(default=False)
    title = models.ForeignKey(Title, null=True, blank=True, on_delete=models.SET_NULL)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    address = models.CharField(max_length=80, null=True, blank=True)
    address2 = models.CharField(max_length=80, null=True, blank=True)
    city = models.CharField(max_length=64, null=True, blank=True)
    state = models.ForeignKey(State, on_delete=models.SET_NULL, null=True, blank=True)
    zip = models.CharField(max_length=10, null=True, blank=True)
    country = models.ForeignKey(Country, on_delete=models.SET_NULL, null=True, blank=True)
    default_phone = models.ForeignKey(UserPhone,
                                      on_delete=models.SET_NULL,
                                      related_name='default_phone',
                                      null=True,
                                      blank=True)
    manager = models.BooleanField(default=False)
    is_login = models.BooleanField(default=False)
    is_twilio_client = models.BooleanField(default=False)
    device_type = models.CharField(max_length=255, null=True, blank=True)
    device_id = models.CharField(max_length=500, null=True, blank=True)
    is_carrier_caller_enabled_for_call = models.BooleanField(default=False)
    is_openvbx_enabled = models.BooleanField(default=False)
    twilio_notification_call_status = models.CharField(max_length=255, null=True, blank=True)
    delete_contacts = models.BooleanField(default=False)
    temppass = models.BooleanField(default=False)
    secret = models.CharField(max_length=40, null=True, blank=True)
    image = ImageField(upload_to=user_profile_image_path, null=True, blank=True)
    contact_radius = models.IntegerField()
    latitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    longitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    last_geocode = models.DateTimeField(null=True, blank=True)
    geocode_count = models.IntegerField(null=True, blank=True, default=0)
    gryphon_number = models.CharField(max_length=10, null=True, blank=True)
    gryphon_pin = models.CharField(max_length=10, null=True, blank=True)
    gryphon_campaign = models.CharField(max_length=10, null=True, blank=True)
    is_client_forward_enable = models.BooleanField(default=False, blank=True)
    is_login_browser = models.CharField(max_length=40, null=True, blank=True)
    is_login_app = models.CharField(max_length=40, null=True, blank=True)
    device_id_app = models.CharField(max_length=500, null=True, blank=True)
    just_my_events = models.BooleanField(default=False)
    hide_my_events = models.BooleanField(default=False)
    cal_followup = models.ForeignKey('UserGoogleCal',
                                     on_delete=models.SET_NULL,
                                     null=True,
                                     blank=True,
                                     related_name='cal_followup')
    office_cal_followup = models.ForeignKey('UserOfficeCal',
                                            on_delete=models.SET_NULL,
                                            null=True,
                                            blank=True,
                                            related_name='office_cal_followup')
    contacts_assigned_count = models.IntegerField(default=0)
    contacts_radius_count = models.IntegerField(default=0)
    contacts_unassigned_count = models.IntegerField(default=0)
    updated = models.DateTimeField()
    user_timezone = models.CharField(max_length=50,
                                     null=True,
                                     blank=True,
                                     default='America/Chicago')
    no_auto_timezone = models.BooleanField(default=False)
    hide_rep_assignment = models.BooleanField(default=False)
    market_manager = models.BooleanField(default=False)
    access_token = models.CharField(max_length=150, null=True, blank=True)
    can_view_company_directory = models.BooleanField(default=False)
    can_make_store_announcement = models.BooleanField(default=False)
    can_add_custom_links = models.BooleanField(default=False)
    can_send_mms = models.BooleanField(default=False)
    can_send_group_sms = models.BooleanField(default=False)
    can_send_sms = models.BooleanField(default=True)
    can_access_call_history = models.BooleanField(default=True)
    can_access_text_message = models.BooleanField(default=True)
    # can_login_multiple_device_dealer_app = models.BooleanField(default=False, blank=True)
    device_udid = models.CharField(max_length=200, null=True, blank=True)
    is_twilio_phone_number_permission = models.BooleanField(default=False, blank=True)
    message_caller_id = models.IntegerField(null=True, blank=True)
    is_facebook_lead_import = models.BooleanField(default=False, blank=True)
    contactmenulist = models.ForeignKey('ContactMenuList',
                                        null=True,
                                        blank=True,
                                        on_delete=models.SET_NULL)
    is_export = models.BooleanField(default=False, blank=True)
    c_android_version = models.CharField(max_length=50, null=True, blank=True)
    b_android_version = models.CharField(max_length=50, null=True, blank=True)
    c_ios_version = models.CharField(max_length=50, null=True, blank=True)
    b_ios_version = models.CharField(max_length=50, null=True, blank=True)
    out_of_store_call = models.BooleanField(default=False, blank=True)
    is_disabled = models.BooleanField(default=False, blank=True)
    is_twilio_phone_number_delete_permission = models.BooleanField(default=False, blank=True)
    is_mail_campaign_permission = models.BooleanField(default=False, blank=True)
    is_start_appointment = models.BooleanField(default=True, blank=True)
    is_delete_personnel = models.BooleanField(default=False, blank=True)
    is_company_activity_stats = models.BooleanField(default=False)
    is_sales_dash_video_permission = models.BooleanField(default=False, blank=True)
    is_followup_office_calendar_checked = models.BooleanField(default=True, blank=True)
    is_followup_google_calendar_checked = models.BooleanField(default=True, blank=True)
    places_cat_list = models.ForeignKey(PlacesCategoryList, on_delete=models.SET_NULL, null=True)
    task_notification_time = models.ForeignKey(TaskNotificationMinuteChoice, default=1, null=True,
                                               on_delete=models.SET_NULL)
    mobile_last_login = models.DateTimeField(null=True, blank=True)
    is_show_task_popup = models.BooleanField(default=True)
    task_popup_disabled = models.BooleanField(default=True)
    google_cal_sync = models.BooleanField(default=True)
    is_telemarketing_manager = models.BooleanField(default=False)
    hide_mobile_appt_popup = models.BooleanField(default=False)
    is_contact_page_as_homepage = models.BooleanField(default=False)
    is_transcription_permission = models.BooleanField(default=False, blank=True)
    is_transcription_settings_permission = models.BooleanField(default=False, blank=True)
    call_review_automation_permission = models.BooleanField(default=False, blank=True)
    event_form = models.ForeignKey('EventForm', on_delete=models.SET_NULL, null=True, blank=True)
    is_automatic_logs_enabled = models.BooleanField(default=False)
    is_2fa_enabled = models.BooleanField(default=False, null=True, blank=True)

    def __str__(self):
        return '%s' % self.fullname()

    # Date : 30-July-2020
    # AIT  - CPV1-139 : Add webinar tracking
    # Desc : The below changes are used to show the webinars count in all type of manager reports.
    def create_report(up, start_date, end_date, **kwargs):
        call_type_in = kwargs.get('call_type_in',
                                  CallType.objects.filter(name__iexact='incoming')[0])
        call_type_out = kwargs.get('call_type_out',
                                   CallType.objects.filter(name__iexact='outgoing')[0])

        r_call_type_in = kwargs.get('r_call_type_in',
                                    TwilioCallType.objects.filter(name__iexact='incoming')[0])
        r_call_type_out = kwargs.get('r_call_type_out',
                                     TwilioCallType.objects.filter(
                                         Q(name__iexact='user_contact') |
                                         Q(name__iexact='browser')).values_list('id', flat=True))

        markets = Market.objects.filter(usermarket__user=up.user)
        # Get the users based on the manager and market manager.
        if up.manager:
            markets = Market.objects.filter(usermarket__company=up.company)
            users = User.objects.filter(userprofile__company=up.company)
        elif not up.manager and up.market_manager:
            users = User.objects.filter(usermarket__company=up.company,
                                        usermarket__market__in=markets)
        else:
            users = User.objects.filter(userprofile__user=up.user)

        users = users.exclude(first_name__iexact='callproof', last_name__iexact='support')
        users = users.exclude(usersetting__name='account_disabled').order_by('first_name',
                                                                             'last_name')
        users = users.distinct()
        markets = list(markets.distinct())

        # Get report type if available
        report_type = kwargs.get('report_type', None)

        if report_type and report_type == constants.MANAGER_PRODUCTION_REPORT_DAILY:
            # If report type is 'Daily' then start and end date should be same.
            report_start_date = start_date.replace(tzinfo=None)
            report_end_date = start_date.replace(tzinfo=None)
        else:
            # Report end date would be end date if its not 'Daily' report.
            report_start_date = start_date
            report_end_date = end_date

        data = {'start_date': report_start_date,
                'end_date': report_end_date,
                'company': up.company,
                'markets': markets,
                'total_activities': 0,
                'active_team_members': 0,
                'inactive_team_members': 0,
                'total_appt_count': 0,
                'total_outbound_calls': 0,
                'total_inbound_calls': 0,
                'total_opp_count': 0,
                'total_followup_count': 0,
                'total_followup_due_count': 0,
                'total_mail_count': 0,
                'total_ef_count': 0,
                'total_new_contacts': 0,
                'user_list': [],
                'active_user_ids': [],
                'inactive_user_ids': [],
                'total_webinar_count': 0
                }

        for user in users:
            appt = Appointment.objects.filter(user=user,
                                              start__gte=start_date,
                                              start__lt=end_date).count()
            # Get the total followup count for the user within a given date range
            followup_count = Followup.objects.filter(user=user,
                                                     start__gte=start_date,
                                                     start__lt=end_date).count()
            # Get the total not completed followup count for the user within a given date range
            followup_due_count = Followup.objects.filter(user=user,
                                                         start__gte=start_date,
                                                         start__lt=end_date)\
                                                 .exclude(completed=True).count()
            opp = Opp.objects.filter(user=user,
                                     created__gte=start_date,
                                     created__lt=end_date).count()
            contacts = Contact.objects.filter(created_by=user,
                                              created__gte=start_date,
                                              created__lt=end_date).count()
            efs = ContactEventForm.objects.filter(user=user,
                                                  created__gte=start_date,
                                                  created__lt=end_date).count()
            emails = EmailMsg.objects.filter(user=user,
                                             sent_date__gte=start_date,
                                             sent_date__lt=end_date).count()
            email_accounts = EmailAccount.objects.filter(user=user,
                                                         company=up.company,
                                                         deleted=False)
            in_calls = Call.objects.filter(user=user,
                                           start__gte=start_date,
                                           start__lt=end_date,
                                           call_type=call_type_in)
            in_rec_calls = TwilioCall.objects.filter(user=user,
                                                     start__gte=start_date,
                                                     start__lt=end_date,
                                                     call_type=r_call_type_in).count()

            out_calls = Call.objects.filter(user=user,
                                            start__gte=start_date,
                                            start__lt=end_date,
                                            call_type=call_type_out)
            out_rec_calls = TwilioCall.objects.filter(user=user,
                                                      start__gte=start_date,
                                                      start__lt=end_date,
                                                      call_type_id__in=r_call_type_out).count()

            if up.company.hide_personal_calls:
                in_calls = in_calls.filter(Q(contact_phone__isnull=False) |
                                           Q(user_phone__isnull=False)).count()
                out_calls = out_calls.filter(Q(contact_phone__isnull=False) |
                                             Q(user_phone__isnull=False)).count()
            else:
                in_calls = in_calls.count()
                out_calls = out_calls.count()

            total_in_calls = in_calls + in_rec_calls

            total_out_calls = out_calls + out_rec_calls

            events = Event.objects.filter(user=user,
                                          created__gte=start_date,
                                          created__lt=end_date).distinct('created__date').count()
            inactivity_days = (end_date - start_date).days - events

            # To get the count of webinar based on start and end date.
            webinar = Webinar.objects.filter(user=user,
                                             created__gte=start_date,
                                             created__lt=end_date).count()

            # Add the emails, opportunities count and remove the past due events count
            # from the total activity count
            activity_count = appt + total_in_calls + total_out_calls + \
                             emails + opp + efs + contacts + webinar

            tmp = {
                'user': user,
                'activity_count': activity_count,
                'appt_count': appt,
                'followup_count': followup_count,
                'followup_due_count': followup_due_count,
                'in_call_count': total_in_calls,
                'out_call_count': total_out_calls,
                'opp_count': opp,
                'mail_count': emails,
                'ef_count': efs,
                'new_contact_count': contacts,
                'inactivity_days': inactivity_days,
                'email_status': email_accounts,
                'webinar_count': webinar
            }

            data['total_appt_count'] += appt
            data['total_outbound_calls'] += total_out_calls
            data['total_inbound_calls'] += total_in_calls
            data['total_opp_count'] += opp
            data['total_followup_count'] += followup_count
            data['total_followup_due_count'] += followup_due_count
            data['total_ef_count'] += efs
            data['total_mail_count'] += emails
            data['total_new_contacts'] += contacts
            data['total_activities'] += activity_count
            data['total_webinar_count'] += webinar
            data['user_list'].append(tmp)

            if activity_count == 0 and events == 0:
                data['inactive_team_members'] += 1
                data['inactive_user_ids'].append(user.id)
            else:
                data['active_team_members'] += 1
                data['active_user_ids'].append(user.id)
        return data

    def show_task_popup(self, current_datetime):
        if self.mobile_last_login:
            last_login_date = self.mobile_last_login.date()
            current_date = current_datetime.date()
            if last_login_date != current_date and not self.is_show_task_popup:
                self.is_show_task_popup = True
                self.save()

        if self.task_popup_disabled:
            return False
        return self.is_show_task_popup

    @staticmethod
    def radius_options(manager=False):
        opts = []

        opts.append([-1, 'All Contacts'])
        opts.append([-2, 'Show Market Contacts'])
        opts.append([0, 'Assigned Contacts'])
        opts.append([10, '&nbsp;-- Plus 10 Mile Radius'])
        opts.append([25, '&nbsp;-- Plus 25 Mile Radius'])
        opts.append([50, '&nbsp;-- Plus 50 Mile Radius'])
        opts.append([100, '&nbsp;-- Plus 100 Mile Radius'])
        opts.append([500, '&nbsp;-- Plus 500 Mile Radius'])
        opts.append([1000, '&nbsp;-- Plus 1000 Mile Radius'])

        return opts

    def geocode_here_user(self):
        output = '\nuser: %s' % self
        address = self.full_address().strip()
        address = re.sub(r'[^a-zA-Z0-9]', '+', address)
        output += '\naddress: %s\n' % address

        # Change the Base URL in the HERE Update the API version [CPV-1 2485]
        if len(address):
            status_code, response_data = geo_code_search_api(address.strip())
            
            if status_code != 200 or not response_data or 'items' not in response_data or len(response_data['items']) == 0:
                heregeocodelog(response_data)
            else:
                position_data = response_data['items'][0]
                if position_data:
                    latitude = str(position_data.get('position', {}).get('lat', ''))
                    longitude = str(position_data.get('position', {}).get('lng', ''))
                    output += '%s, %s' % (latitude, longitude)

                    if latitude and longitude:
                        self.latitude = latitude
                        self.longitude = longitude
                        self.updated = timezone.localtime(timezone.now())

        new_geocode_count = self.geocode_count + 1 if self.geocode_count else 1
        if self.last_geocode:
            self.last_geocode = self.last_geocode + timedelta(hours=(2 * new_geocode_count))
        else:
            self.last_geocode = timezone.localtime(timezone.now()) + \
                                timedelta(hours=(2 * new_geocode_count))
        self.geocode_count = new_geocode_count
        self.save()
        output += '\n'
        return output

    def export_count(self):
        return ExportRun.objects.filter(user=self.user).count()

    def schdule_export_count(self):
        et = ExportType.objects.filter(name='schedule_export_appointment')[0]
        return ExportRun.objects.filter(user=self.user, export_type=et).count()

    def get_last_export(self):
        try:
            er = ExportRun.objects.filter(user=self.user).order_by('-id')[:1][0]
        except:
            er = ''
        return er

    def get_last_schedule_export(self):
        try:
            et = ExportType.objects.filter(name='schedule_export_appointment')[0]
            se = ExportRun.objects.filter(user=self.user, export_type=et).order_by('-id')[:1][0]
        except:
            se = ''
        return se

    def last_activity(self):
        e = Event.objects.filter(user=self.user).order_by('-created').first()
        if e:
            return e.created

        return self.user.last_login

    def to_hash(self):
        if self.updated:
            self.updated = timezone.localtime(self.updated, timezone.get_current_timezone())

        if self.title:
            t = self.title.name
        else:
            t = ''

        data = {'id': self.id,
                'email': self.user.email,
                'user_id': self.user_id,
                'fullname': self.fullname(),
                'title': t,
                'updated': self.updated.strftime('%Y-%m-%d %H:%M:%S'),
                }

        return data

    def insert_delete_action(self, name=None):
        dt = DeleteType.objects.filter(name=name).first()
        if dt:
            da = DeleteAction(company=self.company,
                              user=self.user,
                              delete_type=dt,
                              created=timezone.localtime(timezone.now()))
            da.save()

    def has_google_access_token(self):
        at = AccessToken.objects \
            .filter(user=self.user,
                    expires__gte=timezone.localtime(timezone.now())).first()
        if at is None:
            rt = RefreshToken.objects.filter(user=self.user).first()
            if rt:
                at = rt.get_new_access_token()

        return True if at else False

    def has_office_refresh_token(self):
        from calendar_integration.views import get_office_access_token
        oat = get_office_access_token(self.user)
        return bool(oat)

    def get_events_list(self):
        return Event.objects.filter(user=self.user).order_by('start')

    def get_google_contacts(self):
        return GoogleContact.objects.filter(user=self.user).order_by('id')

    def last_employee_daily_report_hash(self):
        et = EmailType.objects.filter(name='employee_daily_report')[:1][0]
        e = Email.objects.filter(user=self.user, email_type=et).order_by('-created').first()
        if e:
            return e.hashed

    def had_email_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = EmailMsg.objects.filter(user=self.user, sent_date__gte=dt, sent_date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s[:1]
        try:
            s = s[0]
        except:
            s = None
        return s

    def had_call_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatCallDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s[:1]
        try:
            s = s[0]
        except:
            s = None
        return s

    def emails_count_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = EmailMsg.objects.filter(user=self.user, sent_date__gte=dt, sent_date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s.count()
        return s

    def calls_count_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatCallDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s.aggregate(Sum('count'))['count__sum']
        if s is None:
            s = 0
        return s

    def calls_duration_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatCallDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def had_rec_call_between(self, dt, dt2, contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatTwilioCallDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=10),
            When(call_type_id__in=(3, 4), then=0))
        )
        s = s[:1]
        try:
            s = s[0]
        except:
            s = None
        return s

    def had_rec_call_between_awr(self, dt, dt2, contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = TwilioCall.objects.filter(user=self.user, start__gte=dt, start__lt=dt2)
        if contact_type:
            s = s.filter(contact__contact_type=contact_type)
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=11),
            When(call_type_id__in=(3, 4), then=0))
        )
        s = s[:1]
        try:
            s = s[0]
        except:
            s = None
        return s

    def rec_calls_count_between(self, dt, dt2, contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatTwilioCallDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=10),
            When(call_type_id__in=(3, 4), then=0))
        )
        s = s.aggregate(Sum('count'))['count__sum']
        if s is None:
            s = 0
        return s

    def rec_calls_count_between_awr(self, dt, dt2, contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = TwilioCall.objects.filter(user=self.user, start__gte=dt, start__lt=dt2)
        if contact_type:
            s = s.filter(contact__contact_type=contact_type)
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=11),
            When(call_type_id__in=(3, 4), then=0))
        )
        return s.count()

    def rec_calls_duration_between(self, dt, dt2, contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatTwilioCallDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=10),
            When(call_type_id__in=(3, 4), then=0))
        )
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def rec_calls_duration_between_awr(self, dt, dt2, contact_type=None, store_call_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = TwilioCall.objects.filter(user=self.user, start__gte=dt, start__lt=dt2)
        if contact_type:
            s = s.filter(contact__contact_type=contact_type)
        if store_call_type:
            s = s.filter(call_type_id__in=store_call_type)
        s = s.filter(duration__gte=Case(
            When(call_type_id__in=(1, 2), then=11),
            When(call_type_id__in=(3, 4), then=0))
        )
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def had_appt_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatApptDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s[:1]
        try:
            s = s[0]
        except:
            s = None
        return s

    def appts_count_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatApptDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s.aggregate(Sum('count'))['count__sum']
        if s is None:
            s = 0
        return s

    def appts_duration_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatApptDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def had_followup_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatFollowupDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s[:1]
        try:
            s = s[0]
        except:
            s = None
        return s

    def followups_count_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatFollowupDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s.aggregate(Sum('count'))['count__sum']
        if s is None:
            s = 0
        return s

    def followups_duration_between(self, dt, dt2, contact_type=None):
        dt2 = dt2 + timedelta(days=1)
        s = StatFollowupDaily.objects.filter(user=self.user, date__gte=dt, date__lt=dt2)
        if contact_type:
            s = s.filter(contact_type=contact_type)
        s = s.aggregate(Sum('duration'))['duration__sum']
        if s is None:
            s = 0
        return s

    def get_store_phone_id(self):
        us = UserSetting.objects.filter(user=self.user, name='store_phone_caller_id').first()
        if us:
            sp = DealerStorePhone.objects.filter(id=us.value).first()
            if sp:
                return sp.id

    def get_forwarded_phone(self):
        tpn = None

        if self.store:
            for dsp in DealerStorePhone.objects.filter(dealer_store=self.store):
                tpn = TwilioPhoneNumber.objects \
                    .filter(company=self.company,
                            forward_dealer_store_phone=dsp) \
                    .exclude(deleted=True).first()
                if tpn:
                    return tpn

        if tpn is None and self.default_phone:
            tpn = TwilioPhoneNumber.objects \
                .filter(company=self.company,
                        forward_user_phone=self.default_phone) \
                .exclude(deleted=True).first()
        return tpn

    def get_forwarded_client(self, phone_number):
        tpn = TwilioPhoneNumber.objects \
            .filter(company=self.company,
                    phone_number=phone_number) \
            .exclude(deleted=True).first()
        return tpn

    def get_forwarded_sms_phone(self):
        tpn = None
        if self.store:

            for dsp in DealerStorePhone.objects.filter(dealer_store=self.store):
                tpn = TwilioPhoneNumber.objects \
                    .filter(company=self.company,
                            forward_dealer_store_phone=dsp) \
                    .exclude(tollfree=True) \
                    .exclude(deleted=True).first()
                if tpn:
                    return tpn

        if tpn is None and self.default_phone:
            tpn = TwilioPhoneNumber.objects \
                .filter(company=self.company,
                        forward_user_phone=self.default_phone) \
                .exclude(tollfree=True) \
                .exclude(deleted=True).first()
        return tpn

    def get_caller_id_html(self):
        from home.templatetags.home_extras import formatted_phone_number
        cid = None
        us = UserSetting.objects.filter(user=self.user, name='store_phone_caller_id').first()
        if us:
            sp = DealerStorePhone.objects.filter(id=us.value).first()
            if sp and sp.dealer_store.company == self.company:
                cid = TwilioCallerID.objects.filter(dealer_store_phone=sp, validated=True).first()
                if cid:
                    return '%s %s' % (sp.dealer_store.name, formatted_phone_number(sp.phone_number))

        if cid is None and self.default_phone:
            cid = TwilioCallerID.objects.filter(user=self.user,
                                                user_phone=self.default_phone,
                                                validated=True).first()

        if cid is None:
            cid = TwilioCallerID.objects.filter(user=self.user, validated=True).first()
        if cid:
            try:
                pn = self.default_phone.phone_number
            except:
                pn = None
            if pn:
                return '%s' % formatted_phone_number(pn)

        return ''

    def get_message_caller_id(self):
        if self.message_caller_id:
            try:
                tpn = TwilioPhoneNumber.objects \
                    .filter(id=self.message_caller_id) \
                    .exclude(tollfree=True) \
                    .exclude(deleted=True)[0]
            except:
                tpn = None

            if tpn:
                return tpn.name + ' ' + tpn.phone_number

    def get_caller_id(self):
        cid = None
        us = UserSetting.objects.filter(user=self.user, name='store_phone_caller_id').first()
        if us:
            sp = DealerStorePhone.objects.filter(id=us.value).first()
            if sp:
                cid = TwilioCallerID.objects.filter(dealer_store_phone=sp, validated=True).first()

        if cid is None and self.default_phone:
            cid = TwilioCallerID.objects.filter(user=self.user,
                                                user_phone=self.default_phone,
                                                validated=True).first()

        if cid is None:
            cid = TwilioCallerID.objects.filter(user=self.user, validated=True).first()

        return cid

    def clear_tokens(self):
        for at in AccessToken.objects.filter(user=self.user):
            at.delete()
        for rt in RefreshToken.objects.filter(user=self.user):
            rt.delete()

    def remove_google_token(self):
        AccessToken.objects.filter(user=self.user).delete()
        RefreshToken.objects.filter(user=self.user).delete()

    def remove_office_token(self):
        OfficeAccessToken.objects.filter(user=self.user).delete()
        OfficeRefreshToken.objects.filter(user=self.user).delete()

    def created(self):
        return self.company.created.strftime('%m/%d/%y %I:%M %p')

    def tos(self):
        us = UserSetting.objects.filter(user=self.user, name='tos').first()
        return us and int(us.value) == 1

    def add_page_visit(self, name=None):
        p = Page.objects.filter(name=name).first()
        if p is None:
            return

        pv = PageVisit.objects.filter(company=self.company, user=self.user, page=p).first()
        if pv:
            return

        pv = PageVisit(company=self.company,
                       user=self.user,
                       page=p,
                       created=timezone.localtime(timezone.now()))
        pv.save()

    def pull_google_contacts(self):
        pp = re.compile('[^0-9]')
        zp = re.compile('[^-a-zA-Z0-9]')
        np = re.compile('[^-a-zA-Z\ ]')
        ep = re.compile('[^-a-zA-Z0-9\._@]')

        office = PhoneType.objects.filter(name='Office')[:1][0]
        now = timezone.localtime(timezone.now())
        at = AccessToken.objects.filter(user=self.user,
                                        expires__gte=timezone.localtime(timezone.now())).first()

        if at is None:
            rt = RefreshToken.objects.filter(user=self.user).first()
            if rt:
                at = rt.get_new_access_token()

        if at:
            url = 'https://www.google.com/m8/feeds/contacts/default/full?v=3.0&alt=json&max-results=1000&access_token=%s' % at.token
            req = urllib.request.Request(url)
            opener = urllib.request.build_opener(urllib.request.HTTPSHandler(debuglevel=0))
            req = opener.open(req)
            reply = req.read()
            req.close()
            a = json.loads(reply)

            x = 0

            for e in a['feed']['entry']:
                address, address2, city, state, zip, country = None, None, None, None, None, None
                x += 1

                try:
                    first_name = np.sub('', e['gd$name']['gd$givenName']['$t']).strip()[:32]
                except:
                    first_name = None

                try:
                    last_name = np.sub('', e['gd$name']['gd$familyName']['$t']).strip()[:32]
                except:
                    last_name = None

                try:
                    email = ep.sub('', e['gd$email'][0]['address']).strip()[:64].lower()
                except:
                    email = None

                try:
                    addr = e['gd$structuredPostalAddress'][0]
                except:
                    addr = None

                if addr:
                    try:
                        address = addr['gd$street']['$t'].strip()[:80]
                    except:
                        address = None

                    try:
                        address2 = addr['gd$pobox']['$t'].strip()[:80]
                    except:
                        address2 = None

                    try:
                        city = addr['gd$city']['$t'].strip()[:64]
                    except:
                        city = None

                    try:
                        state_abbr = addr['gd$region']['$t'].strip()
                    except:
                        state_abbr = None

                    if state_abbr:
                        province_name = get_user_country_name(self)
                        state = State.objects.filter(abbr=state_abbr, province=province_name).first()
                        if state is None:
                            state = State.objects.filter(name=state_abbr, province=province_name).first()
                    try:
                        zip = zp.sub('', addr['gd$postcode']['$t'])[:10]
                    except:
                        zip = ''

                    if len(zip) == 4:
                        zip = '0%s' % zip

                    try:
                        country_name = addr['gd$country']['$t']
                    except:
                        country_name = None

                    if country_name:
                        country = Country.objects.filter(name=country_name).first()

                google_contact_phones = []

                try:
                    phones = e['gd$phoneNumber']
                except:
                    phones = []

                for p in phones:
                    try:
                        phone = pp.sub('', p['$t'])
                    except:
                        phone = None

                    if phone:
                        if len(phone) == 11 and phone[0] == '1':
                            phone = phone[1:11]
                        elif len(phone) > 10:
                            phone = phone[:10]

                        google_contact_phones.append(phone)

                gc = None

                if email:
                    gc = GoogleContact.objects.filter(email=email).first()

                if gc is None and first_name and last_name:
                    gc = GoogleContact.objects.filter(first_name=first_name,
                                                      last_name=last_name).first()

                if gc is None and first_name and last_name is None:
                    gc = GoogleContact.objects.filter(first_name=first_name,
                                                      last_name=None).first()

                if gc:
                    gc.email = email
                    gc.first_name = first_name
                    gc.last_name = last_name
                    gc.address = address
                    gc.address2 = address2
                    gc.city = city
                    gc.state = state
                    gc.zip = zip
                    gc.country = country
                    gc.updated = now
                else:
                    gc = GoogleContact(user=self.user,
                                       email=email,
                                       first_name=first_name,
                                       last_name=last_name,
                                       address=address,
                                       address2=address2,
                                       city=city,
                                       state=state,
                                       zip=zip,
                                       country=country,
                                       created=now,
                                       updated=now)

                gc.save()

                for p in google_contact_phones:
                    gcp = GoogleContactPhone.objects.filter(google_contact=gc,
                                                            phone_number=p).first()
                    if gcp is None:
                        now = timezone.localtime(timezone.now())
                        gcp = GoogleContactPhone(google_contact=gc,
                                                 phone_type=office,
                                                 phone_number=p,
                                                 created=now,
                                                 updated=now)
                        gcp.save()

    def add_contact_rep(self, c=None):
        if c is None:
            return

        contact = Contact.objects.filter(id=c.id).first()
        if contact is None:
            return

        cr = ContactRep.objects.filter(user=self.user,
                                       contact=contact,
                                       contact__company=contact.company).first()
        if cr:
            return

        if self.company.sales_rep_single_mode:
            cr = ContactRep.objects.filter(contact=contact,
                                           contact__company=contact.company).first()
            if cr is None:
                cr = ContactRep(user=self.user,
                                contact=contact,
                                created=timezone.localtime(timezone.now()))
                try:
                    cr.save()
                except:
                    pass

                if cr and cr.id:
                    contact.assigned = True
                    contact.save()
        else:
            cr = ContactRep(user=self.user,
                            contact=contact,
                            created=timezone.localtime(timezone.now()))
            try:
                cr.save()
            except:
                pass

            if cr and cr.id:
                contact.assigned = True
                contact.save()

    def get_radius_meters(self):
        meters = 0
        if self.contact_radius > 0:
            meters = 1609.344 * float(self.contact_radius + 1)
        return meters

    def roles(self):
        us = UserSetting.objects.filter(user=self.user, name='roles').first()
        return us.value.replace('_', ' ').replace(',', ', ') if us else ''

    def found_us(self):
        # It's not entirely clear what this is trying to do or why it's
        #   looking for found_us and then returning the value of found_us_other
        us = UserSetting.objects.filter(user=self.user, name='found_us').first()
        if us and us.value == 'other':
            us = UserSetting.objects.filter(user=self.user, name='found_us_other').first()
        return us.value.replace('_', ' ') if us else ''

    def employee_phones(self):
        us = UserSetting.objects.filter(user=self.user, name='employee_phones').first()
        return us.value if us else ''

    def team_size(self):
        us = UserSetting.objects.filter(user=self.user, name='team_size').first()
        return us.value if us else ''

    def signup_phone(self):
        us = UserSetting.objects.filter(user=self.user, name='signup_phone').first()
        return us.value if us else ''

    def signup_title(self):
        us = UserSetting.objects.filter(user=self.user, name='signup_title').first()
        return us.value if us else ''

    def account_disabled(self):
        if self.company.disabled:
            return True
        us = UserSetting.objects.filter(user=self.user, name='account_disabled').first()
        if us:
            return True
        return False

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))

    def get_assigned_contacts(self):
        if self.contact_radius == -1:
            contacts = [c for c in Contact.objects.filter(company=self.company)]
            return contacts

        ids = [str(cr.contact_id) for cr in ContactRep.objects.filter(user=self.user).order_by('-id')]
        where = 'id IN (%s)' % ','.join(ids) if len(ids) > 0 else 'id IN (0)'
        return [c for c in Contact.objects.filter(company=self.company).extra(where=[where]).order_by('-id')]

    def get_radius_contacts(self):
        if self.contact_radius > 0:
            try:
                latitude = self.last_location().latitude
            except:
                latitude = None

            if latitude is None:
                try:
                    latitude = self.latitude
                except:
                    latitude = None

            try:
                longitude = self.last_location().longitude
            except:
                longitude = None

            if longitude is None:
                try:
                    longitude = self.longitude
                except:
                    longitude = None

            if latitude and longitude:
                sql = """
                  SELECT cp_contact.id AS id
                  FROM cp_contact
                  WHERE (  ST_DistanceSphere(
                  st_makepoint(%s, %s),
                  st_makepoint(cp_contact.longitude, cp_contact.latitude)) )/%s < %s
                """ % (longitude, latitude, settings.METER_TO_MILES, self.contact_radius)
                contacts = list(Contact.objects.raw(sql))
                return contacts
        return []

    def get_all_contact_ids(self):
        return [str(c.id) for c in self.get_all_contacts()]

    def get_all_contacts(self):
        if self.manager:
            return Contact.objects.filter(company=self.company)

        contacts = [c for c in self.get_assigned_contacts()]
        for c in self.get_radius_contacts():
            if c not in contacts:
                contacts.append(c)

        if self.unassigned_leads():
            for c in self.company.unassigned_leads():
                contacts.append(c)

        return contacts

    def is_clocked_in(self):
        work = Work.objects.filter(user=self.user, duration=0).order_by('-created').first()
        return True if work else False

    def sync_calls(self):
        us = UserSetting.objects.filter(user=self.user, name='sync_calls').first()
        return int(us.value) if us else 3600

    def sync_stats(self):
        us = UserSetting.objects.filter(user=self.user, name='sync_stats').first()
        return int(us.value) if us else 1800

    def sync_events(self):
        us = UserSetting.objects.filter(user=self.user, name='sync_events').first()
        return int(us.value) if us else 1800

    def sync_appointments(self):
        us = UserSetting.objects.filter(user=self.user, name='sync_appointments').first()
        return int(us.value) if us else 3600

    def calculate_contacts_distance(self):
        us = UserSetting.objects.filter(user=self.user, name='calculate_contacts_distance').first()
        return int(us.value) if us else 1800

    def sync_contacts(self):
        us = UserSetting.objects.filter(user=self.user, name='sync_contacts').first()
        return int(us.value) if us else 28800

    def is_sync_gps(self):
        us = UserSetting.objects.filter(user=self.user, name='is_sync_gps').first()
        return int(us.value) if us else 0

    def sync_gps(self):
        us = UserSetting.objects.filter(user=self.user, name='sync_gps').first()
        return int(us.value) if us else 900

    def track_gps(self):
        us = UserSetting.objects.filter(user=self.user, name='gps').first()
        return True if us and us.value == '1' else False

    def unassigned_leads(self):
        us = UserSetting.objects.filter(user=self.user, name='unassigned_leads').first()
        return True if us and us.value == '1' else False

    def end_prev_appts(self):
        try:
            user = self.user
        except:
            user = None
        if user is None:
            return
        for a in Appointment.objects.filter(user=user, duration=0):
            a.auto_end()

    def emails_count_yesterday(self):
        count = EmailMsg.objects.filter(user=self.user,
                                        sent_date__gte=get_yesterday(),
                                        sent_date__lt=get_midnight()).aggregate(Count('id'))['id__count']
        if count is None:
            count = 0
        return count

    def eventform_count_yesterday(self):
        count = ContactEventForm.objects.filter(user=self.user,
                                                created__gte=get_yesterday(),
                                                created__lt=get_midnight()).aggregate(Count('id'))['id__count']
        if count is None:
            count = 0
        return count

    def eventform_count_yesterday_ct(self, contact_type=None):
        sql = """
            select * from cp_contacteventform
            LEFT JOIN cp_contact
            ON cp_contacteventform.contact_id = cp_contact.id
            LEFT JOIN cp_contacttype
            ON cp_contact.contact_type_id = cp_contacttype.id
            where cp_contacteventform.user_id=%s and cp_contacteventform.created >= '%s' and cp_contacteventform.created < '%s' and cp_contacttype.id=%s
        """ % (self.user.id, get_yesterday(), get_midnight(), contact_type.id)
        cef = list(ContactEventForm.objects.raw(sql))
        count = len(cef)
        return count

    def emails_count_monthly(self):
        count = StatEmailDaily.objects \
            .filter(user=self.user,
                    date__gte=get_monthfirstday(),
                    date__lt=get_midnight()) \
            .aggregate(Count('id'))['id__count']
        if count is None:
            count = 0
        return count

    def emails_count_yesterday_ct(self, contact_type=None):
        count = EmailMsg.objects \
            .filter(contact_type=contact_type,
                    user=self.user,
                    sent_date__gte=get_yesterday(),
                    sent_date__lt=get_midnight()) \
            .aggregate(Count('id'))['id__count']
        if count is None:
            count = 0
        return count

    # cell calls
    def calls_count_yesterday(self):
        missed = CallType.objects.filter(name='missed')[:1][0]
        count = StatCallHourly.objects \
            .exclude(call_type=missed) \
            .filter(user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    # cell calls monthly
    def calls_count_monthly(self):
        missed = CallType.objects.filter(name='missed')[:1][0]
        count = StatCallDaily.objects \
            .exclude(call_type=missed) \
            .filter(user=self.user,
                    date__gte=get_monthfirstday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    def calls_count_yesterday_ct(self, contact_type=None):
        missed = CallType.objects.filter(name='missed')[:1][0]
        count = StatCallHourly.objects \
            .exclude(call_type=missed) \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    def calls_duration_yesterday(self):
        missed = CallType.objects.filter(name='missed')[:1][0]
        duration = StatCallHourly.objects \
            .exclude(call_type=missed) \
            .filter(user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    def calls_duration_yesterday_ct(self, contact_type=None):
        missed = CallType.objects.filter(name='missed')[:1][0]
        duration = StatCallHourly.objects \
            .exclude(call_type=missed) \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    # twilio
    def rec_calls_count_yesterday(self):
        count = StatTwilioCallHourly.objects \
            .filter(user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    def rec_calls_count_yesterday_ct(self, contact_type=None):
        count = StatTwilioCallHourly.objects \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    def rec_calls_duration_yesterday(self):
        duration = StatTwilioCallHourly.objects \
            .filter(user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    def rec_calls_duration_yesterday_ct(self, contact_type=None):
        duration = StatTwilioCallHourly.objects \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    # Date : 17-Aug-2020
    # AIT  - CPV1-218 : Add Webinar Tracking to Manager Summary report
    # Desc : The below section is used to get the webinar's yesterday count.
    def webinars_count_yesterday(self):
        count = StatWebinarHourly.objects \
            .filter(Q(user=self.user,
                      date__gte=get_yesterday(),
                      date__lt=get_midnight())) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    # Date : 17-Aug-2020
    # AIT  - CPV1-218 : Add Webinar Tracking to Manager Summary report
    # Desc : The below section is used to get the webinar's monthly count.
    def webinars_count_monthly(self):
        count = StatWebinarDaily.objects \
            .filter(user=self.user,
                    date__gte=get_monthfirstday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    # Date : 06-Aug-2020
    # AIT  - CPV1-139 : Add webinar tracking
    # Desc : The below section is used to get the webinar's yesterday count.
    def webinars_count_yesterday_ct(self, contact_type=None):
        count = StatWebinarHourly.objects \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    # Date : 06-Aug-2020
    # AIT  - CPV1-139 : Add webinar tracking
    # Desc : The below section is used to get the webinar's yesterday duration count.
    def webinars_duration_yesterday(self):
        duration = StatWebinarHourly.objects \
            .filter(user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    # Date : 06-Aug-2020
    # AIT  - CPV1-139 : Add webinar tracking
    # Desc : The below section is used to get the webinar's contact type count.
    def webinars_duration_yesterday_ct(self, contact_type=None):
        duration = StatWebinarHourly.objects \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    # appts
    def appointments_count_yesterday(self):
        count = StatApptHourly.objects \
            .filter(user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    # appts
    def appointments_count_monthly(self):

        count = StatApptDaily.objects \
            .filter(user=self.user,
                    date__gte=get_monthfirstday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    def appointments_count_yesterday_ct(self, contact_type=None):
        count = StatApptHourly.objects \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('count'))['count__sum']
        if count is None:
            count = 0
        return count

    def appointments_duration_yesterday(self):
        duration = StatApptHourly.objects \
            .filter(user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    def appointments_duration_yesterday_ct(self, contact_type=None):
        duration = StatApptHourly.objects \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    # followups
    def followups_count_yesterday(self):
        count = StatFollowupHourly.objects \
            .filter(user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Count('id'))['id__count']
        if count is None:
            count = 0
        return count

    def followups_count_yesterday_ct(self, contact_type=None):
        count = StatFollowupHourly.objects \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Count('id'))['id__count']
        if count is None:
            count = 0
        return count

    # followups today
    def followups_count_today(self):
        count = Followup.objects \
            .filter(user=self.user,
                    start__gte=get_midnight(),
                    start__lt=get_tomorrow()) \
            .aggregate(Count('id'))['id__count']
        if count is None:
            count = 0
        return count

    # followups next seven days
    def followups_count_nextsevendays(self):
        count = Followup.objects \
            .filter(user=self.user,
                    start__gte=get_midnight(),
                    start__lt=get_nextsevendays()) \
            .aggregate(Count('id'))['id__count']
        if count is None:
            count = 0
        return count

    def followups_duration_yesterday(self):
        duration = StatFollowupHourly.objects \
            .filter(user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    def last_app_logout(self):
        name = 'mobile_logout'
        try:
            et = EventType.objects.filter(company=self.company, name=name)[:1][0]
        except:
            return ''
        event = Event.objects.filter(company=self.company,
                                     user=self.user,
                                     event_type=et).order_by('-start').first()
        if event is None:
            return ''
        return event.start

    def followups_duration_yesterday_ct(self, contact_type=None):
        duration = StatFollowupHourly.objects \
            .filter(contact_type=contact_type,
                    user=self.user,
                    date__gte=get_yesterday(),
                    date__lt=get_midnight()) \
            .aggregate(Sum('duration'))['duration__sum']
        if duration is None:
            duration = 0
        return duration

    def employee_unsubscribe(self):
        return UserSetting.objects.filter(user=self.user, name='employee_unsubscribe').first()

    def manager_daily_report(self):
        return UserSetting.objects.filter(user=self.user, name='manager_daily_report').first()

    def manager_summary_report(self):
        return UserSetting.objects.filter(user=self.user, name='manager_summary_report').first()

    def manager_production_report_daily(self):
        return UserSetting.objects.filter(user=self.user,
                                          name='manager_production_report_daily').first()

    def manager_production_report_week(self):
        return UserSetting.objects.filter(user=self.user,
                                          name='manager_production_report_week').first()

    def manager_production_report_month(self):
        return UserSetting.objects.filter(user=self.user,
                                          name='manager_production_report_month').first()

    def employee_daily_report(self):
        return UserSetting.objects.filter(user=self.user, name='employee_daily_report').first()

    def employee_followup_reminder(self):
        return UserSetting.objects.filter(user=self.user, name='employee_followup_reminder').first()

    def appointment_report(self):
        return UserSetting.objects.filter(user=self.user, name='appointment_report').first()

    def get_area_code(self):
        user_phone = UserPhone.objects.filter(user=self.user_id).order_by('-updated').first()
        if user_phone is None:
            return ''
        pn = user_phone.phone_number
        if len(pn) == 10:
            return pn[0:3]
        if len(pn) == 11:
            return pn[1:3]
        return ''

    def last_appointment(self):
        return Appointment.objects.filter(user=self.user_id).order_by('-id').first()

    def last_apk_version(self):
        return APKVersion.objects.filter(user=self.user_id,
                                         application_name__isnull=True).order_by('-id').first()

    def last_ios_version(self):
        return IOSVersion.objects.filter(user=self.user,
                                         application_name__isnull=True).order_by('-id').first()

    def last_apk_version_bclock(self):
        version = APKVersion.objects.filter(user=self.user_id,
                                            application_name='bclock').order_by('-id')[:1]
        try:
            version = version[0]
            if version.android_apk_version == '-1':
                return version.cp_version
            else:
                return version.android_apk_version
        except:
            version = None
        return version

    def last_ios_version_bclock(self):
        return IOSVersion.objects.filter(user=self.user,
                                         application_name='bclock').order_by('-id').first()

    def last_location(self):
        return Location.objects.filter(user=self.user_id).order_by('-id').first()

    def last_nine_appointments(self):
        return Appointment.objects.filter(user=self.user_id).order_by('-id')[1:10]

    def last_ten_appointments(self):
        return Appointment.objects.filter(user=self.user_id).order_by('-id')[0:10]

    def last_nine_locations(self):
        return Location.objects.filter(user=self.user_id).order_by('-id')[1:10]

    def last_ten_locations(self):
        return Location.objects.filter(user=self.user_id).order_by('-id')[0:10]

    def download_count(self):
        return Download.objects.filter(user=self.user_id).aggregate(Count('id'))['id__count']

    def is_manager(self):
        return self.manager

    def fullname(self):
        return '%s %s' % (self.user.first_name, self.user.last_name)

    def email(self):
        return '%s' % self.user.email

    def get_user_phones(self):
        return self.user.userphone_set.all()

    def get_auto_detection(self):
        try:
            no_auto_timezone = self.no_auto_timezone
        except:
            no_auto_timezone = False

        return no_auto_timezone

    def get_user_timezone(self):
        try:
            user_timezone = self.user_timezone
        except:
            user_timezone = None

        if user_timezone:
            timezone_name = user_timezone
        else:
            timezone_name = 'US/Mountain'

        return '%s' % timezone_name

    def rerank(self):
        try:
            if self.company.id == 4966:  # - not want ranking data for norco account
                return False
        except:
            pass

        user = self.user
        company = self.company

        now = timezone.localtime(timezone.now())

        rt_day = RankType.objects.get(name='day')
        rt_week = RankType.objects.get(name='week')
        rt_month = RankType.objects.get(name='month')

        rank_group_users = RankGroupUser.objects.select_related('rank_group').filter(company=company, user=user)

        for rgus in rank_group_users:
            if rgus.rank_group.date_mode == 0:
                days1 = now - timedelta(days=1)
                days7 = now - timedelta(days=7)
                days30 = now - timedelta(days=30)
            elif rgus.rank_group.date_mode == 1:
                days1 = timezone.localtime(timezone.now()).replace(hour=0, minute=0, second=0, microsecond=0)
                days7 = previous_weekday(now, rgus.rank_group.first_day)
                days30 = first_of_month(now)

            rts = [[rt_day, days1],
                   [rt_week, days7],
                   [rt_month, days30]]

            user_ids = RankGroupUser.objects.filter(company=company, rank_group=rgus.rank_group) \
                .values_list('user_id', flat=True)
            if not user_ids:
                continue

            for rt in rts:
                user_pts = {}
                user_ranks = {}
                rnk = 1

                contact_event_forms = ContactEventForm.objects.filter(
                    company_id=company.id,
                    user_id__in=user_ids,
                    created__gte=rt[1]
                ).values('user_id').annotate(points=Sum('points'))

                for event_forms in contact_event_forms:
                    user_pts[event_forms['user_id']] = int(event_forms['points'])

                events = Event.objects.filter(
                    company_id=company.id,
                    user_id__in=user_ids,
                    start__gte=rt[1]
                ).values('user_id').annotate(points=Coalesce(Sum('points'), 0))

                for event in events:
                    try:
                        user_pts[event['user_id']] += int(event['points'])
                    except:
                        user_pts[event['user_id']] = int(event['points'])

                for user_id, value in sorted(iter(list(user_pts.items())),
                                             key=lambda k_v: (k_v[1], k_v[0]),
                                             reverse=True):
                    user_ranks[user_id] = rnk
                    rnk += 1
                for user_id in user_ids:
                    try:
                        user_ranks[user_id]
                    except:
                        user_ranks[user_id] = rnk
                        rnk += 1
                rank_users = []
                for user_id in user_ids:
                    try:
                        pts = user_pts[user_id]
                    except:
                        pts = 0
                    rk = user_ranks[user_id]
                    rank_users.append(RankUser(company=company,
                                               user_id=user_id,
                                               rank_group=rgus.rank_group,
                                               rank_type=rt[0],
                                               date=now,
                                               points=pts,
                                               rank=rk))
                RankUser.objects.bulk_create(rank_users)

            rgus.rank_group.last = now
            rgus.rank_group.save()

    def is_support(self):
        return str(self.user.first_name).lower() == 'callproof' and \
               str(self.user.last_name).lower() == 'support'

    def add_event(self,
                  name=None,
                  contact=None,
                  other_user=None,
                  call=None,
                  start=None,
                  duration=None,
                  badge=None,
                  google_place=None,
                  tc=None,
                  tsms=None,
                  cef=None,
                  created=None,
                  appointment=None,
                  followup=None,
                  video_message=None):

        if self.is_support():
            return

        points = 0

        et = EventType.objects.filter(company=self.company, name=name).first()
        if et:
            if created is None:
                created = timezone.localtime(timezone.now())

            points = EventType.objects.filter(company_id=self.company_id, id=et.id).aggregate(
                points=Coalesce(Sum('eventtypepoint__point__value'), 0))['points']

            if points is None:
                points = 0

            # check exists
            e = Event.objects.filter(company=self.company,
                                     user=self.user,
                                     event_type=et,
                                     created=created,
                                     popular=created,
                                     contact=contact,
                                     other_user=other_user,
                                     call=call,
                                     start=start,
                                     duration=duration,
                                     badge=badge,
                                     google_place=google_place,
                                     tc=tc,
                                     tsms=tsms,
                                     cef=cef,
                                     points=points,
                                     video_message=video_message).first()
            if e is None:
                # does not already exist
                e = Event(company=self.company,
                          user=self.user,
                          event_type=et,
                          created=created,
                          popular=created,
                          contact=contact,
                          other_user=other_user,
                          call=call,
                          start=start,
                          duration=duration,
                          badge=badge,
                          google_place=google_place,
                          tc=tc,
                          tsms=tsms,
                          cef=cef,
                          points=points,
                          appointment=appointment,
                          followup=followup,
                          video_message=video_message)
                e.save()

                company = self.company
                company.last_activity = e.created
                company.save()

                if points != 0:
                    self.rerank()

    def full_address(self):
        state = self.state.abbr if self.state else ''
        address = self.address if self.address else ''
        address2 = self.address2 if self.address2 else ''
        city = self.city if self.city else ''
        zip = self.zip if self.zip else ''

        addr = '%s %s %s %s %s' % (address, address2, city, state, zip)
        return addr.replace('  ', ' ').strip()

    # To get the user primary location search type
    def get_primary_location_search(self):
        get_primary_location = Company.objects.filter(id=self.company.id)
        primary_location = get_primary_location[0].primary_location_search_type
        return primary_location

    def chat_bot_setting(self):
        user_setting = UserSetting.objects.filter(user=self.user, name='chat_bot').first()
        return True if user_setting and user_setting.value == '1' else False

    def twilio_call_summary(self):
        user_setting = UserSetting.objects.filter(user=self.user, name='ai_call_summary').first()
        return True if user_setting and user_setting.value == '1' else False

    def ai_prompt_setting(self):
        user_setting = UserSetting.objects.filter(user=self.user, name='ai_prompt_edit').first()
        return True if user_setting and user_setting.value == '1' else False


class CallType(models.Model):
    name = models.CharField(max_length=8)

    def __str__(self):
        return '%s' % self.name

    def pretty_name(self):
        return '%s' % self.name.replace('_', '').title()


class ContactType(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    image = ImageField(upload_to=contact_type_image_path, null=True, blank=True)
    is_default = models.BooleanField(default=False)
    # Date : 23-10-2019
    # AIT - CAL -16 : WEB - PROJECT - Create new Contact Type "Internal Staff"
    # Desc : reference_contact_type_name and position attributes are added in the model.
    # reference_contact_type_name column holds the exact name of the contact type
    # and position column holds the position of the contact type
    reference_contact_type_name = models.CharField(max_length=64)
    position = models.IntegerField()

    def __str__(self):
        return '%s' % self.name

    def contact_count(self):
        try:
            c = Contact.objects.filter(contact_type=self).aggregate(Count('id'))['id__count']
        except:
            c = 0
        return c

    @staticmethod
    def contact_types():
        return ['Client', 'Lead', 'Prospect', 'Other']


class Category(models.Model):
    name = models.CharField(max_length=32, unique=True)

    class Meta:
        verbose_name_plural = 'categories'

    def __str__(self):
        return '%s' % self.name


class Work(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    created = models.DateTimeField()
    duration = models.IntegerField(null=True, blank=True, default=0)
    latitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    longitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)

    def __str__(self):
        return '%s %s %s %s' % (self.user.first_name,
                                self.user.last_name,
                                self.created,
                                self.duration)

    def formatted_start(self):
        return '%s' % \
               timezone.localtime(self.created,
                                  timezone.get_current_timezone()).strftime('%Y-%m-%d %H:%M:%S')


class ContactInfoEmail(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact = models.ForeignKey('Contact', on_delete=models.CASCADE)
    email = models.EmailField(blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s - %s' % (self.contact.__str__(), self.email)


class ContactPhone(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact = models.ForeignKey('Contact', on_delete=models.CASCADE)
    phone_type = models.ForeignKey(PhoneType, on_delete=models.CASCADE)
    phone_number = models.CharField(max_length=15, validators=[MinLengthValidator(7)])
    ext = models.CharField(max_length=6, blank=True)
    country_code = models.CharField(max_length=4)
    activated = models.DateField(null=True, blank=True)
    eligible = models.DateField(null=True, blank=True)
    call_result = models.ForeignKey('TwilioCallResult',
                                    on_delete=models.CASCADE,
                                    null=True,
                                    blank=True)
    last_contacted = models.DateTimeField(null=True, blank=True)
    hidden = models.NullBooleanField(null=True, blank=True)
    carrier_name = models.CharField(max_length=100, null=True, blank=True)
    caller_name = models.CharField(max_length=100, null=True, blank=True)
    do_not_call = models.NullBooleanField(null=True, blank=True)
    dealer_store = models.ForeignKey('DealerStore',
                                     on_delete=models.SET_NULL,
                                     null=True,
                                     blank=True)
    model = models.CharField(max_length=255, null=True, blank=True)
    unknown = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    lookup_updated_on = models.DateField(null=True, blank=True)
    personnel = models.ForeignKey('ContactPersonnel',
                                  on_delete=models.CASCADE,
                                  null=True,
                                  blank=True)
    call_count = models.IntegerField(null=True, blank=True, default=0)
    is_dealer_imported = models.BooleanField(default=False)
    imported_date = models.DateTimeField(null=True, blank=True)
    description = models.CharField(max_length=500, null=True, blank=True)
    contact_type = models.ForeignKey(ContactType, on_delete=models.CASCADE)
    is_active_lead = models.BooleanField(default=False)
    is_in_dnd = models.BooleanField(default=False)
    is_in_dnc = models.BooleanField(default=False)
    user = models.ForeignKey(User, on_delete=models.SET_NULL, null=True, blank=True)
    forward_incoming_to = models.CharField(max_length=15, null=True)
    fcc_complain = models.BooleanField(null=True)  # null: not checked, false: no complain,  True: has complain

    def __str__(self):
        return '%s - %s - %s' % (self.contact.__str__(),
                                 self.phone_number,
                                 self.phone_type.__str__())

    def get_personnels(self):
        return ContactPersonnel.objects.filter(contactphonepersonnel__contactphone=self,
                                               contact=self.contact)
    
    # These changes are used to get current peoples
    def get_current_personnels(self):
        return ContactPersonnel.objects.filter(contactphonepersonnel__contactphone=self,
                                               contact=self.contact.id, moved_to__isnull=True)

    def to_hash(self):
        try:
            if self.last_contacted:
                self.last_contacted = timezone.localtime(self.last_contacted,
                                                         timezone.get_current_timezone())
            last_contacted = self.last_contacted.strftime('%Y-%m-%d %H:%M:%S')
        except:
            last_contacted = ''

        try:
            if self.activated:
                self.activated = timezone.localtime(self.activated, timezone.get_current_timezone())
            activated = self.activated.strftime('%Y-%m-%d %H:%M:%S')
        except:
            activated = ''

        try:
            if self.eligible:
                self.eligible = timezone.localtime(self.eligible, timezone.get_current_timezone())
            eligible = self.eligible.strftime('%Y-%m-%d %H:%M:%S')
        except:
            eligible = ''

        try:
            call_result = self.call_result.result
        except:
            call_result = ''

        try:
            dealer_store = self.dealer_store.name
        except:
            dealer_store = ''

        unknown = 1 if self.unknown else 0
        do_not_call = 1 if self.do_not_call else 0
        hidden = 1 if self.hidden else 0
        model = self.model if self.model else ''

        data = {'id': self.id,
                'last_contacted': last_contacted,
                'unknown': unknown,
                'do_not_call': do_not_call,
                'contact_id': self.contact_id,
                'contact': self.contact.fullname(),
                'phone_type': self.phone_type.name,
                'phone_number': self.phone_number,
                'ext': self.ext,
                'activated': activated,
                'eligible': eligible,
                'call_result': call_result,
                'hidden': hidden,
                'dealer_store': dealer_store,
                'model': model,
                'updated': self.updated.strftime('%Y-%m-%d %H:%M:%S'),
                'created': self.created.strftime('%Y-%m-%d %H:%M:%S'),
                }

        return data

    def check_new_upgrade(self, user):
        a = self.activated
        try:
            call_buy_days = self.company.get_call_buy_days()
        except:
            call_buy_days = 14

        a14 = a - timedelta(days=call_buy_days)
        fc = FollowupCall.objects.filter(created__gte=a14,
                                         created__lt=a,
                                         contact_phone=self,
                                         user=user).first()
        if fc:
            fc.new_upgrade = True
            try:
                a = datetime.combine(a, datetime.min.time())
                a = timezone.make_aware(a, timezone.utc)
            except:
                pass
            fc.upgrade_time = (a - fc.created).total_seconds() / 60.0 / 60.0 / 24.0
            fc.save()

    def use_gryphon(self):
        if self.activated is None:
            return True
        min_age = timezone.localtime(timezone.now()) - \
                  relativedelta(months=self.company.get_transaction_months())
        if self.activated < min_age.date():
            return True
        return False

    def last_contacted_date(self):
        if self.last_contacted:
            return self.last_contacted.strftime('%b %e, %Y')
        return ''

    def has_twilio_call(self):
        tc = TwilioCall.objects.filter(contact_phone=self).first()
        twilio_log('contact phone has twilio call')
        return tc is not None

    def has_twilio_call_after_contact(self):
        tc = TwilioCall.objects.filter(contact_phone=self, start__gte=self.created).first()
        return tc is not None

    # Added by Aashish for Josh FB lead work-11Sep19
    def recent_note_created_after_contact(self):
        note = ContactNote.objects.filter(contact=self.contact,
                                          company=self.contact.company,
                                          created__gte=self.created).order_by('-created').first()
        if note:
            try:
                note = note.simplenote()
            except:
                note = note.note
            return note
        return ''

    # Added by Aashish for Josh FB lead work-11Sep19
    def recent_msgs_sent_after_contact(self):
        msgs = TwilioSMS.objects.filter(contact=self.contact,
                                        company=self.contact.company,
                                        start__gte=self.created).order_by('-start').first()
        if msgs:
            try:
                msg = msgs.msg
            except:
                msg = ''
            return msg
        return ''

    def last_twilio_call(self):
        twilio_log('contact phone last twilio call')
        return TwilioCall.objects.filter(contact_phone=self).order_by('-id').first()

    def activated_date(self):
        if self.activated:
            return self.activated.strftime('%b %e, %Y')
        return ''

    def eligible_date(self):
        if self.eligible:
            return self.eligible.strftime('%b %e, %Y')
        return ''

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))

    def get_store_twilio_phone_number(self):
        tpn = None
        try:
            tpn = TwilioPhoneNumber.objects.filter(company=self.company,
                                                   name__iexact=self.dealer_store.name)[0]
        except:
            tpn = None
        return tpn

    def get_incoming_calls_count(self):
        return TwilioCall.objects.filter(company=self.company,
                                         contact_phone=self,
                                         call_type_id__in=[3, 4]).count()

    def ident(self):
        # First, identify the Contact associated with this ContactPhone record.
        # ???: Much of this code seems redundant. I don't think it's possible for a
        #   ContactPhone to have a contact_id associated with it that doesn't exist
        #   as a Contact because it's a foreign key constraint.
        contact = Contact.objects.filter(id=self.contact_id).first()
        if contact is None:
            return 'contact not found'

        out = '%s %s' % (self, contact)
        thirty_days_ago = timezone.localtime(timezone.now()) - timedelta(days=30)
        now = timezone.localtime(timezone.now())

        # For each Call made within the last 30 days by any user in this Company where:
        #   a) the Call hasn't been associated with a user yet and
        #   b) the phone_number called matches this ContactPhone number
        for call in Call.objects.filter(company=self.company,
                                        contact_phone=None,
                                        user_phone=None,
                                        google_place=None,
                                        start__gte=thirty_days_ago,
                                        phone_number=self.phone_number):

            # Associate the Call with this ContactPhone
            out += str(call)
            call.contact_phone = self
            call.lookup_count = call.lookup_count + 1
            call.last_lookup = now
            call.save()

            # Update the Contact.last_contacted date if:
            #   a) it hasn't been set yet or
            #   b) if the start of the call is more recent than the last_contacted date
            if contact.last_contacted is None or contact.last_contacted < call.start:
                contact.last_contacted = call.start
                contact.updated = now
                contact.save()

            # Set the updated date on the ContactPersonnel record associated with this ContactPhone
            personnel = ContactPersonnel.objects.filter(id=self.personnel_id).first()
            if personnel:
                personnel.updated = now
                personnel.save()

            # Add an event to the UserProfile of the user associated with the Call,
            #   indicating that a contact_call was made.
            # If the user associated with this call isn't a ContactRep for this Contact,
            #   then add them as one.
            # ???: I believe this means that if a rep calls a Contact they're not already
            #   a ContactRep for, they will be added.
            try:
                user_profile = call.user.userprofile
            except:
                user_profile = None
            if user_profile:
                user_profile.add_event(name='contact_call_%s' % call.call_type.name,
                                       contact=contact,
                                       call=call,
                                       start=call.start,
                                       duration=call.duration,
                                       created=call.start)
                user_profile.add_contact_rep(contact)

        # Iterate over the Twilio calls made in the last 30 days within the company
        #   which haven't been identified yet and have the same phone number as this Contact.
        for twilio_call in TwilioCall.objects.filter(company=self.company,
                                                     contact_phone=None,
                                                     user_phone=None,
                                                     google_place=None,
                                                     start__gte=thirty_days_ago,
                                                     caller=self.phone_number):

            # Associate the TwilioCall with this ContactPhone
            out += str(twilio_call)
            twilio_call.contact_phone = self
            twilio_call.lookup_count = twilio_call.lookup_count + 1
            twilio_call.last_lookup = now
            twilio_call.save()

            # Update the Contact.last_contacted date if:
            #   a) it hasn't been set yet or
            #   b) if the start of the call is more recent than the last_contacted date
            if contact.last_contacted is None or contact.last_contacted < twilio_call.start:
                contact.last_contacted = twilio_call.start
                contact.updated = now
                contact.save()

            # Set the updated date on the ContactPersonnel record associated with this ContactPhone
            try:
                personnel = ContactPersonnel.objects.filter(id=self.personnel_id)[:1][0]
            except:
                personnel = None
            if personnel:
                personnel.updated = now
                personnel.save()

            # Add an event to the UserProfile of the user associated with the Call,
            #   indicating that a contact_call was made.
            # If the user associated with this call isn't a ContactRep for this Contact,
            #   then add them as one.
            # ???: I believe this means that if a rep calls a Contact they're not already
            #   a ContactRep for, they will be added.
            try:
                user_profile = twilio_call.user.userprofile
            except:
                user_profile = None
            if user_profile:
                user_profile.add_event(name='contact_call_%s' % twilio_call.call_type.name,
                                       contact=contact,
                                       tc=twilio_call,
                                       start=twilio_call.start,
                                       duration=twilio_call.duration,
                                       created=twilio_call.start)
                user_profile.add_contact_rep(contact)

        # Return the text output, representing what happened so it can be logged
        return out

    def recent_messages(self):
        return TwilioSMS.objects.filter(contact=self.contact,
                                        company=self.contact.company,
                                        start__gte=self.created).order_by('-start')[:5]

    def fcc_dnc_api(self, fcc_api_setting=None):
        if fcc_api_setting is None:
            fcc_api_setting = FccAPISetting.objects.filter(company=self.company,
                                                           enable=True).first()

        # Check the fcc_api_setting is exists or not
        if fcc_api_setting:
            if self.fcc_complain is not None:
                # if fcc api already checked for this contact
                # we are passing default value to skip the api call
                fcc = FccDNCAPI(fcc_api_setting, self.phone_number, default=self.fcc_complain)
            else:
                fcc = FccDNCAPI(fcc_api_setting, self.phone_number)
                self.fcc_complain = fcc.has_complain
                self.save()
            # These changes are used to check fcc_api_setting record is exist or not
            if fcc_api_setting:
                if not self.do_not_call and fcc_api_setting.mark_dnc and fcc.has_complain:
                    self.do_not_call = True
                    self.save()
            return fcc

        return None

    def get_phonenumber_message_consent(self):
        """
        Function get the contact phone is opt-in or opt-out
        @return: Return the True or False
        """

        phone_numbers = PhoneNumberMessageConsent.objects.filter(phone_number=self.phone_number).first()
        phone_number_status = phone_numbers.is_opt_in if phone_numbers is not None else False
        return phone_number_status


class ContactNoteSourceType(models.Model):
    name = models.CharField(max_length=100)


class ContactNote(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact = models.ForeignKey('Contact', on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    note = models.TextField(max_length=4096)
    created = models.DateTimeField()
    sourcetype = models.ForeignKey(ContactNoteSourceType,
                                   null=True,
                                   blank=True,
                                   on_delete=models.SET_NULL)
    source_id = models.IntegerField(null=True, blank=True)

    def __str__(self):
        return '%s - %s - %s' % (self.contact.__str__(), self.note[:256], self.created)

    # - to extract contact id if saved while company wide
    def simplenote(self):
        try:
            note = self.note
            grp = re.findall(r'!@![\d]+!@!', note)
            grp = grp[len(grp) - 1]
            id = re.findall(r'[\d]+', grp)[0]
            c = Contact.objects.filter(id=id, company=self.company)[:1][0]
            note = re.sub(r'!@![\d]+!@!', '', note)
            note = '%s (added to [%s])' % (note, c.fullname())
            return note
        except:
            return note

    def to_hash(self):
        try:
            if self.created:
                self.created = timezone.localtime(self.created, timezone.get_current_timezone())
            created = self.created.strftime('%Y-%m-%d %H:%M:%S')
        except:
            created = ''

        try:
            created_by = self.user.userprofile.fullname()
        except:
            created_by = ''

        try:
            created_by_id = self.user_id
        except:
            created_by_id = ''

        try:
            created_by_email = self.user.email
        except:
            created_by_email = ''

        data = {'id': self.id,
                'created': created,
                'created_by_id': created_by_id,
                'created_by_email': created_by_email,
                'created_by': created_by,
                'contact_id': self.contact_id,
                'contact': self.contact.fullname(),
                'company_id': self.contact.contact_company_id,
                'company': self.contact.contact_company.name,
                'note': self.note,
                }

        return data

    def after_source_track(self):
        devdate = datetime.strptime('11/26/2018', '%m/%d/%Y')
        devdate = timezone.make_aware(devdate, pytz.timezone('UTC'))
        return self.created >= devdate


class ContactCompany(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    primary_contact = models.ForeignKey('Contact', on_delete=models.SET_NULL, null=True, blank=True)
    name = models.CharField(max_length=256)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s' % self.name

    def get_duplicates(self):
        return DuplicateContactCompany.objects.filter(contact_company=self,
                                                      never_merge=False).order_by('id')

    def get_contacts(self):
        return Contact.objects.filter(contact_company=self).order_by('first_name')

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))

    def truncated_name(self):
        return self.name[:48]

    def to_hash(self):
        if self.updated:
            self.updated = timezone.localtime(self.updated, timezone.get_current_timezone())
        if self.created:
            self.created = timezone.localtime(self.created, timezone.get_current_timezone())
        if not self.primary_contact_id:
            self.primary_contact_id = ''
        data = {'id': self.id,
                'primary_contact': self.primary_contact_id,
                'name': self.name,
                'updated': self.updated.strftime('%Y-%m-%d %H:%M:%S'),
                'created': self.created.strftime('%Y-%m-%d %H:%M:%S'),
                }
        return data


class ContactPersonnel(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact = models.ForeignKey('Contact', on_delete=models.CASCADE)
    first_name = models.CharField(max_length=75)
    last_name = models.CharField(max_length=32)
    email = models.CharField(max_length=64, null=True, blank=True, default='')
    personnel_notes = models.TextField(null=True, blank=True)
    cell_phone = models.CharField(max_length=15)
    title = models.TextField()
    peoplerole = models.ForeignKey('PeopleRole', null=True, blank=True, on_delete=models.SET_NULL)
    last_contacted = models.DateTimeField(null=True, blank=True)
    image = ImageField(upload_to=contact_personnel_image_path, null=True, blank=True)
    is_disabled = models.BooleanField(default=False)
    moved_to = models.IntegerField()
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def fullname(self):
        return '%s %s' % (self.first_name, self.last_name)

    def to_hash(self):
        last_contacted = ''
        updated = ''
        if self.updated:
            try:
                updated = \
                    timezone.localtime(self.updated,
                                       timezone.get_current_timezone()) \
                        .strftime('%Y-%m-%d %H:%M:%S')
            except:
                pass

                last_contacted = ''
        if self.last_contacted:
            try:
                last_contacted = \
                    timezone.localtime(self.last_contacted,
                                       timezone.get_current_timezone()) \
                        .strftime('%Y-%m-%d %H:%M:%S')
            except:
                pass

        data = {"id": self.id,
                "fullname": self.fullname(),
                "first_name": self.first_name if self.first_name else '',
                "last_name": self.last_name if self.last_name else '',
                "title": self.title if self.title else '',
                "last_contacted": last_contacted,
                "role": self.peoplerole.name if self.peoplerole else '',
                "email": self.email if self.email else '',
                "updated": updated,
                }

        return data

    def contact_phones(self):
        return ContactPhone.objects.filter(contactphonepersonnel__personnel=self)


class ContactCallFrequency(models.Model):
    name = models.CharField(max_length=30)
    value = models.IntegerField()


class Contact(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_company = models.ForeignKey(ContactCompany,
                                        null=True,
                                        blank=True,
                                        on_delete=models.CASCADE)
    created_by = models.ForeignKey(User, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, on_delete=models.CASCADE)
    title = models.CharField(max_length=64, null=True, blank=True, default='')
    first_name = MyCharField(max_length=32, null=True, blank=True)
    last_name = models.CharField(max_length=32, null=True, blank=True)
    email = models.CharField(max_length=64, null=True, blank=True, default='')
    address = models.CharField(max_length=80, null=True, blank=True, default='')
    address2 = models.CharField(max_length=80, null=True, blank=True, default='')
    city = models.CharField(max_length=64, null=True, blank=True, default='')
    state = models.ForeignKey(State, on_delete=models.SET_NULL, null=True, blank=True)
    zip = models.CharField(max_length=10, null=True, blank=True, default='')
    country = models.ForeignKey(Country, on_delete=models.SET_NULL, null=True, blank=True)
    website = models.CharField(max_length=255, null=True, blank=True, default='')
    latitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    longitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    last_contacted = models.DateTimeField(null=True, blank=True)
    default_phone = models.ForeignKey(ContactPhone,
                                      related_name='default_phone',
                                      null=True,
                                      blank=True,
                                      on_delete=models.SET_NULL)
    image = ImageField(upload_to=contact_image_path, null=True, blank=True)
    account = models.CharField(max_length=80, null=True, blank=True, default='')
    invoice = models.CharField(max_length=64, null=True, blank=True)
    last_geocode = models.DateTimeField(null=True, blank=True)
    geocode_count = models.IntegerField(null=True, blank=True, default=0)
    unknown = models.BooleanField(default=False)
    assigned = models.BooleanField(default=False)
    do_not_sms = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    place = models.ForeignKey('GooglePlace', on_delete=models.CASCADE)
    district = models.CharField(max_length=100, null=True, blank=True)
    sales_type = models.CharField(max_length=100, null=True, blank=True)
    related_esn = models.CharField(max_length=50, null=True, blank=True)
    related_product = models.CharField(max_length=100, null=True, blank=True)
    handset_type = models.CharField(max_length=100, null=True, blank=True)
    sync_with_ac = models.CharField(max_length=20, null=True, blank=True)
    zap_facebook_lead = models.CharField(max_length=20, null=True, blank=True)
    business_type = models.TextField(blank=True, null=True)
    employee_count = models.CharField(max_length=50, blank=True, null=True)
    annual_sales = models.CharField(max_length=125, blank=True, null=True)
    county = models.CharField(max_length=255, blank=True, null=True)
    is_pinned = models.BooleanField(default=False)
    position = models.IntegerField(blank=True, null=True)

    class Meta:
        indexes = [models.Index(fields=['place'], name='cp_contact_place_id_index')]

    def __str__(self):
        fn = ''
        if self.first_name and len(self.first_name) > 0:
            fn = self.first_name
        ln = ''
        if self.last_name and len(self.last_name) > 0:
            ln = self.last_name
        return ('%s %s' % (fn, ln)).strip()

    def get_events(self, user_profile):
        event_types = tuple(EventType.objects.filter((Q(name="outgoing_videomessage") | Q(name="get_team_status")),
                                                    company=self.company).values_list('id', flat=True))
        
        events = Event.objects.filter(contact=self,
                                      user__userprofile__hide_my_events=False).order_by("-created")

        if len(event_types) == 2:
            events = events.exclude(event_type=event_types[0]).exclude(event_type=event_types[1])

        if user_profile.just_my_events:
            events = events.filter(user=user_profile.user)
        return events

    def get_contact_companies_phone(self):
        if self.company.people_tab:
            office = PhoneType.objects.filter(name='Office')[:1][0]
            return self.contactphone_set.filter(
                Q(contactphonepersonnel__personnel__isnull=True) |
                Q(phone_type=office)).distinct('id')
        else:
            return self.contactphone_set.all()

    def set_account_auto_inc(self):  # - call this at the time of add contact only
        if self.company.is_account_inc and \
                (not self.account or self.account == '' or self.account is None):
            self.account = self.company.account_inc + 1
            return True
        return False

    def forlpop_set_account_auto_inc(self, company):  # - call this at the time of add contact only
        if company.is_account_inc and \
                (not self.account or self.account == '' or self.account is None):
            self.account = company.account_inc + 1
            return True
        return False

    def to_hash(self):

        from cfields.templatetags.cfields_extras import get_cfield_value, get_cfield_value_id

        try:
            created_by = self.created_by.userprofile.fullname()
        except:
            created_by = ''

        try:
            created_by_id = self.created_by_id
        except:
            created_by_id = ''

        try:
            created_by_email = self.created_by.email
        except:
            created_by_email = ''

        try:
            if self.last_contacted:
                self.last_contacted = timezone.localtime(self.last_contacted,
                                                         timezone.get_current_timezone())
            last_contacted = self.last_contacted.strftime('%Y-%m-%d %H:%M:%S')
        except:
            last_contacted = ''

        try:
            default_phone = self.default_phone.to_hash()
        except:
            default_phone = {}

        try:
            state = self.state.name
        except:
            state = ''

        try:
            country = self.country.name
        except:
            country = ''

        title = self.title if self.title else ''
        assigned = 1 if self.assigned else 0
        unknown = 1 if self.unknown else 0
        do_not_sms = 1 if self.do_not_sms else 0
        invoice = self.invoice if self.invoice else ''
        city = self.city if self.city else ''
        website = self.website if self.website and self.website != 'None' else ''
        account = self.account if self.account else ''
        zip = self.zip if self.zip else ''
        first_name = self.first_name if self.first_name else ''
        last_name = self.last_name if self.last_name else ''
        email = self.email if self.email and self.email != 'None' else ''
        address = self.address if self.address else ''
        address2 = self.address2 if self.address2 else ''

        try:
            latitude = str(float(self.latitude))
        except:
            latitude = ''

        try:
            longitude = str(float(self.longitude))
        except:
            longitude = ''

        custom_fields = []

        cfields = self.company.get_custom_fields_list('contact',
                                                      show_hidden=False,
                                                      show_img_fields=False)

        factory = RequestFactory()
        request = factory.get('/')
        request.view_name = 'fake'

        for cf in cfields:
            if cf.cfield:
                cfield = {'id': cf.id,
                          'name': cf.cfield.name,
                          'value': get_cfield_value(cf.cfield, self),
                          'value_id': get_cfield_value_id(cf.cfield, self)}
            else:
                cfield = {'id': cf.id,
                          'name': cf.name,
                          'value': get_cfield_value(cf, self),
                          'value_id': get_cfield_value_id(cf, self)}
            custom_fields.append(cfield)

        reps = []
        for u in self.get_sales_reps():
            try:
                up = u.userprofile
            except:
                up = None
            if up:
                reps.append(up.to_hash())

        contact_phones = [cp.to_hash() for cp in ContactPhone.objects.filter(company=self.company,
                                                                             contact=self)]

        if self.updated:
            self.updated = timezone.localtime(self.updated, timezone.get_current_timezone())

        if self.created:
            self.created = timezone.localtime(self.created, timezone.get_current_timezone())

        data = {'id': self.id,
                'company': self.contact_company.name,
                'contact_phones': contact_phones,
                'created_by': created_by,
                'created_by_id': created_by_id,
                'created_by_email': created_by_email,
                'contact_type': self.contact_type.name,
                'title': title,
                'first_name': first_name,
                'last_name': last_name,
                'email': email,
                'address': address,
                'address2': address2,
                'city': city,
                'state': state,
                'zip': zip,
                'country': country,
                'website': website,
                'latitude': latitude,
                'longitude': longitude,
                'last_contacted': last_contacted,
                'default_phone': default_phone,
                'account': account,
                'invoice': invoice,
                'unknown': unknown,
                'assigned': assigned,
                'do_not_sms': do_not_sms,
                'updated': self.updated.strftime('%Y-%m-%d %H:%M:%S'),
                'created': self.created.strftime('%Y-%m-%d %H:%M:%S'),
                'custom_fields': custom_fields,
                'reps': reps,
                }

        return data

    # Sort the people alphabetically
    def get_contact_personnel(self, order_by='first_name', limit=100):
        return ContactPersonnel.objects \
                   .filter(contact=self) \
                   .exclude(is_disabled=True) \
                   .order_by(order_by)[:limit]

    def get_contact_images(self):
        images = []
        for ci in ContactImage.objects.filter(company=self.company,
                                              contact=self).order_by('-id')[:50]:
            images.append(ci)
        return images

    def get_email_msgs(self):
        # AIT - 11-04-2020
        # Urgent fix for Email sync
        pers = self.get_contact_personnel(order_by='first_name')
        email_list = []
        email_list.append(self.email)
        for i in pers:
            email_list.append(i.email)

        additional_email = ContactInfoEmail.objects.filter(company=self.company, contact=self)
        for j in additional_email:
            email_list.append(j.email)

        company = self.company
        msgs = []

        # for email in email_list:
        for m in EmailMsg.objects.filter(company=company, contact=self).order_by('-sent_date')[:50]:
            msgs.append(m)

        return msgs

    def get_contact_email_message(self):

        email_message_unique = set()
        email_address = EmailMessageAddress.objects.filter(company=self.company, contact=self).values_list('email_message')
        if email_address:
            for message in EmailMsg.objects.filter(id__in=email_address):
                email_message_unique.add(message)
        for e_message in EmailMsg.objects.filter(company=self.company, contact=self):
            email_message_unique.add(e_message)

        # Sorting the email messages on created date reverse order
        email_message_unique_list = list(email_message_unique)
        sorted_results = sorted(email_message_unique_list, key=lambda result_message: result_message.created, reverse=True)

        return sorted_results

    def get_email_msgs_count(self):
        return EmailMsg.objects.filter(company=self.company, contact=self).count()

    def get_files(self):
        files = []
        for cuf in ContactUserFile.objects.filter(company=self.company,
                                                  contact=self).order_by('-id')[:50]:
            files.append(cuf.user_file)
        return files

    def recent_sms(self):
        return TwilioSMS.objects.filter(company=self.company, contact=self).order_by('-id')[:10]

    def mail_name(self):
        s = str(self.contact_company)
        if len(s) == 0:
            return False
        return s

    def selected_appt_notes(self):
        n = 'Meeting'
        if self.fullname():
            n = '%s with %s' % (n, self.fullname())
        n = '%s at %s' % (n, self.contact_company.name)
        return n

    def get_opps_count(self):
        return len(self.get_opps())

    def get_opps(self):
        opps = []
        opps_list = Opp.objects.filter(company=self.company).prefetch_related('opppersonnel_set')
        opps_list = opps_list.filter(Q(contact=self) | Q(oppcontact__contact=self)).distinct('id')
        for o in opps_list:
            opp = {}
            try:
                opp['id'] = o.id
                opp['user'] = o.user
                opp['contact'] = o.contact
                opp['opptype'] = o.opp_type
                opp['oppstage'] = o.opp_stage
                opp['probability'] = o.probability
                opp['value'] = o.value
                opp['derived'] = o.value * o.probability / 100
                opp['close_date'] = o.close_date.strftime('%b %d, %Y')
                opp['cl_date'] = o.close_date
                opp['updated'] = o.updated
                opp['opp_name'] = o.opp_name if o.opp_name else ''
                opp['personnels'] = o.opppersonnel_set.all()
                opp['created_date'] = o.created.strftime('%b %d, %Y')
                opps.append(opp)
            except:
                pass

        return opps

    def get_duplicates(self):
        return DuplicateContact.objects.filter(contact=self, never_merge=False)

    def duplicate_count(self):
        return DuplicateContact.objects.filter(contact=self, never_merge=False).count()

    def get_txt_msgs(self):
        return TwilioSMS.objects.filter(contact=self).order_by('-id')

    def get_contact_event_forms(self):
        return ContactEventForm.objects.filter(contact=self).order_by('-created')

    def get_contact_event_forms_limit(self):
        return ContactEventForm.objects.filter(contact=self).order_by('-created')[:10]

    def last_contacted_date(self):
        if self.last_contacted:
            return self.last_contacted.strftime('%b %e, %Y')
        return ''

    def created_short(self):
        return self.created.strftime('%Y-%m-%d')

    def get_m_name(self):
        name = ('%s %s' % (self.first_name, self.last_name)).strip()
        if len(name) == 0:
            name = self.contact_company.name.strip()
        return name

    def get_m_title(self):
        if not self.company.people_tab:
            name = ('%s %s' % (self.first_name, self.last_name)).strip()
        else:
            name = ''
        if len(name) == 0:
            name = self.contact_company.name.strip().replace(':', '').replace('/', '')
        url = ''
        try:
            im = get_thumbnail(self.image, '48x48', crop='center')
        except:
            im = None
        if im:
            url = '%s' % im.url
        else:
            url = ''
        if url == '':
            try:
                im = get_thumbnail(self.contact_type.image, '48x48', crop='center')
            except:
                im = None
            if im:
                url = '%s' % im.url
            else:
                url = ''
        return '%s|%s|%s' % (self.id, name, url)

    def get_notes(self):
        return ContactNote.objects.filter(contact=self, company=self.company).order_by('-created')

    def get_parent_company_notes(self):
        parent_company = self.title
        if parent_company is None or parent_company == 'None' or parent_company == '':
            return ContactNote.objects.filter(contact=self).order_by('-created')[:25]
        contacts = Contact.objects.filter(company=self.company, title=parent_company)
        return ContactNote.objects.filter(contact__in=contacts).order_by('-created')[:25]

    def recent_note(self):
        note = ContactNote.objects.filter(contact=self,
                                          company=self.company) \
            .order_by('-created') \
            .first()
        if note:
            try:
                note = note.simplenote()
            except:
                note = note.note
            return note
        return ''

    def geocode_here(self):
        output = '\ncontact: %s' % self
        address = self.full_address().strip()
        address = re.sub(r'[^a-zA-Z0-9]', '+', address)

        output += '\naddress: %s\n' % address

        if len(address):
            # Upgrade new here geocode API on 2024-05-15
            status_code, response_data = geo_code_search_api(address.strip())

            if status_code != 200 or not response_data or 'items' not in response_data or len(response_data['items']) == 0:
                heregeocodelog(response_data)
            else:
                position_data = response_data['items'][0]
                if position_data:
                    latitude = str(position_data.get('position', {}).get('lat', ''))
                    longitude = str(position_data.get('position', {}).get('lng', ''))

                    output += '%s, %s\n' % (latitude, longitude)
                    if latitude and longitude:
                        self.latitude = latitude
                        self.longitude = longitude
                        self.updated = timezone.localtime(timezone.now())

        new_geocode_count = self.geocode_count + 1 if self.geocode_count else 1

        if self.last_geocode:
            self.last_geocode = self.last_geocode + timedelta(days=(2 * new_geocode_count))
        else:
            self.last_geocode = timezone.localtime(timezone.now()) + \
                                timedelta(days=(2 * new_geocode_count))
        self.geocode_count = new_geocode_count

        try:
            self.save()
        except:
            output += 'save failed: %s' % str(self)

        return output

    # Apply POI data to the contact
    def set_poi_data(self, business_type=None, county=None, employee_count=None, annual_sales=None):
        try:
            business_type = business_type
        except:
            business_type = None

        try:
            county = county
        except:
            county = None

        try:
            employee_count = employee_count
        except:
            employee_count = None

        try:
            annual_sales = annual_sales
        except:
            annual_sales = None

        if business_type and not self.business_type:
            self.business_type = business_type

        if county and not self.county:
            self.county = county

        if employee_count and not self.employee_count:
            self.employee_count = employee_count

        if annual_sales and not self.annual_sales:
            self.annual_sales = annual_sales

    def for_select(self):
        n = self.fullname()
        if n == 'None None':
            n = ''
        if len(n) > 18:
            n = n[:18]
        contact_company = self.contact_company
        if contact_company and contact_company.name:
            n = '%s %s' % (n, contact_company.name)
        n = n.strip()
        return n

    def fullname(self):
        f = '' if self.first_name is None or self.first_name == 'None' else self.first_name
        l = '' if self.last_name is None or self.last_name == 'None' else self.last_name
        n = '%s %s' % (f, l)
        n = n.strip()
        return '%s' % n

    def is_primary_contact(self):
        contact_company = ContactCompany.objects.filter(primary_contact=self).first()
        return True if contact_company else False

    def has_sales_reps(self):
        return ContactRep.objects.filter(contact=self,
                                         contact__company=self.company) \
                   .aggregate(Count('id'))['id__count'] > 0

    def get_sales_reps(self):
        sql = """
          SELECT 
            auth_user.id AS id, 
            auth_user.first_name, 
            auth_user.last_name
          FROM auth_user
            LEFT JOIN cp_contactrep
                ON auth_user.id = cp_contactrep.user_id
            LEFT JOIN cp_contact
                ON cp_contactrep.contact_id = cp_contact.id
            LEFT JOIN cp_userprofile
                ON auth_user.id = cp_userprofile.user_id
          WHERE cp_contact.id = %s
            AND cp_userprofile.company_id = %s
          ORDER BY auth_user.first_name
        """ % (self.id, self.company_id)

        return list(User.objects.raw(sql))

    def get_last_contacted_sales_rep_id(self):
        cr = ContactRep.objects.filter(contact=self.id).order_by('-id').first()
        return cr.user_id if cr else ''

    def get_last_assigned_rep_name(self):
        cr = ContactRep.objects.filter(contact=self.id).order_by('-id').first()
        return cr.user.get_full_name() if cr else 'Unassigned'

    def sales_rep_short_list(self):
        crs = ContactRep.objects.filter(contact=self, contact__company=self.company)
        count = crs.count()
        if count > 3:
            crs = crs[:3]
        names = ', '.join([cr.user.userprofile.fullname() for cr in crs])
        if count > 3:
            names = '%s and %s other%s' % (names, count - 3, '' if count - 3 == 1 else 's')
        return '%s' % names

    def sales_rep_ids(self):
        ids = []
        for cr in ContactRep.objects.filter(contact=self, contact__company=self.company):
            ids.append(str(cr.user_id))
        return '%s' % ','.join(unique(ids))

    def contact_name(self):
        return '%s' % self

    def map_name(self):
        cn = 'No Company Name' if (self.contact_company is None) else ('%s' % self.contact_company.name)
        fn = '' if (self.first_name == '' or self.first_name is None) else ('%s' % self.first_name)
        ln = '' if (self.last_name == '' or self.last_name is None) else ('%s' % self.last_name)
        if len(fn) > 0 or len(ln) > 0:
            fn = '<br />%s' % fn
        return '%s%s %s' % (cn, fn, ln)

    def full_address(self):
        try:
            state = self.state.abbr
        except:
            state = ''
        address = str(self.address).strip() if self.address else ''
        address2 = str(self.address2).strip() if self.address2 else ''
        city = str(self.city).strip() if self.city else ''
        zip = str(self.zip).strip() if self.zip else ''

        addr = '%s %s %s %s %s' % (address, address2, city, state, zip)
        return addr.replace('  ', ' ').strip()

    def get_contact_phones(self):
        duplicate_contacts_log(f"Contact get_contact_phones")
        phones = self.contactphone_set.all()
        duplicate_contacts_log(f"Contact get_contact_phones")
        duplicate_contacts_log(f"phones: {phones}")
        duplicate_contacts_log(f"phones length: {len(phones)}")
        return phones

    def get_additional_emails(self):
        return ContactInfoEmail.objects.filter(contact=self).order_by('-id')

    def get_contact_phones_last3(self):
        return ContactPhone.objects.filter(contact=self).order_by('-updated')[:3]

    def get_calls(self):
        phone_ids = list(self.contactphone_set.values_list('id', flat=True))
        if not phone_ids:
            return Call.objects.none()
        return Call.objects.filter(contact_phone_id__in=phone_ids).order_by('-start')

    def get_rcalls(self):
        phone_ids = list(self.contactphone_set.values_list('id', flat=True))
        phone_ids = ['0'] if not phone_ids else phone_ids
        return TwilioCall.objects.filter(Q(contact=self) | Q(contact_phone_id__in=phone_ids)).order_by('-start')

    def get_followups(self):
        return self.followup_set.order_by('-start').all()

    def get_appointments(self):
        return Appointment.objects.filter(contact=self, scheduled=False).order_by('-start')

    def get_incoming_calls_count(self):
        return TwilioCall.objects.filter(company=self.company,
                                         contact=self,
                                         call_type_id__in=[3, 4]).count()

    def get_outgoing_calls_count(self):
        return TwilioCall.objects.filter(company=self.company,
                                         contact=self,
                                         call_type_id__in=[1, 2]).count()

    def get_last_appointments(self):
        return Appointment.objects.filter(contact=self, scheduled=False).order_by('-id')[:1]

    def get_last_followup(self):
        try:
            return Followup.objects.filter(contact=self).order_by('-id')[0]
        except:
            return False

    def get_next_followups(self):
        return Followup.objects.filter(contact=self, start__gte=timezone.localtime(timezone.now()))

    def get_future_appointments(self):
        return Appointment.objects.filter(contact=self, scheduled=True).order_by('-start')

    def get_last_contacted_pretty(self):
        if self.last_contacted and len(str(self.last_contacted)) > 1:
            try:
                return timezone.localtime(self.last_contacted,
                                          timezone.get_current_timezone()) \
                    .strftime('%b %d, %Y %I:%M %p')
            except:
                return 0
        else:
            return 0

    def get_last_contacted(self):
        if self.last_contacted and len(str(self.last_contacted)) > 1:
            return self.last_contacted.strftime('%Y-%m-%d %H:%M:%S')
        else:
            return ''

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))

    def get_last_contacted_week(self):
        if self.last_contacted and len(str(self.last_contacted)) > 1:
            now = timezone.localtime(timezone.now())
            diff = now - self.last_contacted
            days = diff.days
            if days < 7:  # - visited in current week
                return 1
            elif 7 <= days < 14:  # - visited in last week
                return 2
            else:  # - more than a weeks
                return 3
        else:
            return 3  # - not visited

    def get_employee_count_range(self):
        emp_count = convert_count_db_to_dropdown(self.employee_count)
        if emp_count:
            for name, value in employee_count_dropdown():
                if value == emp_count:
                    return name
        return self.employee_count or None

    def get_annual_sales_range(self):
        an_sales = convert_sales_db_to_dropdown(self.annual_sales)
        if an_sales:
            for name, value in annual_sales_dropdown():
                if value == an_sales:
                    return name
        return self.annual_sales or None

    def get_heads_up_notes(self):
        """
        Fetch Contact Heads up notes.
        :return: Notes values or None.
        """
        from cfields.views import find_entity_heads_up_notes
        return find_entity_heads_up_notes(self)


class Call(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    local_id = models.IntegerField()
    call_type = models.ForeignKey(CallType, on_delete=models.CASCADE)
    phone_number = models.CharField(max_length=11)
    start = models.DateTimeField()
    duration = models.IntegerField(null=True, blank=True, default=0)
    contact_phone = models.ForeignKey(ContactPhone,
                                      null=True,
                                      blank=True,
                                      on_delete=models.SET_NULL)
    user_phone = models.ForeignKey(UserPhone, null=True, blank=True, on_delete=models.SET_NULL)
    google_place = models.ForeignKey('GooglePlace',
                                     null=True,
                                     blank=True,
                                     on_delete=models.SET_NULL)
    last_lookup = models.DateTimeField(null=True, blank=True)
    lookup_count = models.IntegerField(null=True, blank=True, default=0)
    contact_id = models.IntegerField(null=True, blank=True)

    def __str__(self):
        return '%s %s %s %s %s' % (self.user.first_name,
                                   self.user.last_name,
                                   self.phone_number,
                                   self.start,
                                   self.duration)

    def to_hash(self):
        try:
            if self.start:
                self.start = timezone.localtime(self.start, timezone.get_current_timezone())
            created = self.start.strftime('%Y-%m-%d %H:%M:%S')
        except:
            created = ''

        try:
            rep = self.user.userprofile.to_hash()
        except:
            rep = {}

        try:
            contact_id = self.contact_phone.contact_id
        except:
            contact_id = ''

        try:
            contact = self.contact_phone.contact.fullname()
        except:
            contact = ''

        try:
            contact_phone_id = self.contact_phone_id
        except:
            contact_phone_id = ''

        try:
            contact_phone = self.contact_phone.phone_number
        except:
            contact_phone = ''

        try:
            user_phone_id = self.user_phone_id
        except:
            user_phone_id = ''

        try:
            user_phone = self.user_phone.phone_number
        except:
            user_phone = ''

        data = {'id': self.id,
                'created': created,
                'contact_id': contact_id,
                'contact': contact,
                'contact_phone_id': contact_phone_id,
                'contact_phone': contact_phone,
                'user_phone_id': user_phone_id,
                'user_phone': user_phone,
                'phone_number': self.phone_number,
                'rep': rep,
                'call_type': self.call_type.name,
                'duration': self.duration,
                }

        return data

    def call_length(self):
        if self.duration:
            return get_duration_time(self.duration)
        return ''

    def is_followup(self):
        fc = FollowupCall.objects.filter(call=self).first()
        return True if fc else False

    def add_followup_call(self):
        if self.call_type.name != 'outgoing':
            return

        cp = self.contact_phone
        c = cp.contact
        company = c.company

        f = Followup.objects \
            .filter(user=self.user, contact=c) \
            .exclude(completed=True) \
            .order_by('-start') \
            .first()

        if f:
            fc = FollowupCall.objects \
                .filter(company=company,
                        followup=f,
                        user=self.user,
                        contact=c,
                        contact_phone=cp,
                        call=self,
                        created=self.start).first()
            if fc is None:
                response_time = float((self.start - f.start).total_seconds()) / 60.0 / 50.0 / 24.0

                if response_time > 9999.99:
                    response_time = 9999.99

                fc = FollowupCall(company=company,
                                  followup=f,
                                  response_time=response_time,
                                  user=self.user,
                                  store=self.user.userprofile.store,
                                  contact=c,
                                  contact_phone=cp,
                                  call=self,
                                  created=self.start)
                fc.save()

    def start_time(self):
        return '%s%s' % (int(self.start.strftime('%I')), self.start.strftime(':%M%P').lower())

    def rep_start_time(self):
        user_timezone = self.user.userprofile.get_user_timezone()
        user_tz = pytz.timezone(user_timezone)
        if user_tz is not None:
            masked_start_time = timezone.localtime(self.start, user_tz)
        else:
            masked_start_time = self.start

        return '%s%s' % (int(masked_start_time.strftime('%I')),
                         masked_start_time.strftime(':%M%P').lower())

    def get_m_title(self):
        id = 0
        name = ''
        if self.contact_phone:
            contact = self.contact_phone.contact
            id = contact.id
            name = ('%s %s' % (contact.first_name, contact.last_name)).strip()
            if len(name) == 0:
                name = contact.contact_company.name.strip()
        elif self.user_phone:
            user = self.user_phone.user
            id = user.id
            name = ('%s %s' % (user.first_name, user.last_name)).strip()
        elif self.google_place:
            name = self.google_place.name
            id = self.google_place.id
        url = ''
        try:
            im = get_thumbnail(self.contact_phone.contact.image, '48x48', crop='center')
        except:
            im = None

        if im is None:
            try:
                im = get_thumbnail(self.contact_phone.contact.contact_type.image,
                                   '48x48',
                                   crop='center')
            except:
                im = None
        if im is None:
            try:
                im = get_thumbnail(self.user.image, '48x48', crop='center')
            except:
                im = None
        if im is None:
            try:
                im = get_thumbnail(self.user.title.image, '48x48', crop='center')
            except:
                im = None
        if im:
            url = '%s' % im.url

        return '%s|%s|%s|%s|%s|%s|0' % (self.id, self.entity(), id, self.phone_number, name, url)

    def entity(self):
        if self.contact_phone:
            return 'c'
        elif self.user_phone:
            return 'u'
        elif self.google_place:
            return 'g'
        return 'x'

    def ident(self):
        pn = self.phone_number

        if not ident_phone(self):
            if len(pn) == 11:
                ident_phone(self, pn[1:11])
            elif len(pn) == 10:
                ident_phone(self, pn[3:10])
        new_lookup_count = self.lookup_count + 1
        self.last_lookup = self.last_lookup + timedelta(hours=(new_lookup_count * 12))
        self.lookup_count = new_lookup_count
        self.save()

    def get_call_contacts(self):
        account_people_name_list = []
        # Get the contacts related to the call
        if self.contact_phone:
            account_personnel_list = self.contact_phone.get_personnels()
            # Get the full name of the contact and append to a list
            for person in account_personnel_list:
                account_people_name_list.append(person.fullname())

        if len(account_people_name_list) > 4:
            # Return contacts full name when the call has more than 4 contacts.
            first_four_people_name_list = []
            for index in range(4):
                first_four_people_name_list.append('%s' % account_people_name_list[index])
            return '<b>%s and %s others</b>' % (', '.join(first_four_people_name_list),
                                                len(account_people_name_list) - 4)
        elif account_people_name_list:
            # Return contacts full name when the call has less than 4 contacts.
            return '<b>%s</b>' % (', '.join(account_people_name_list))

        # Return empty string when the call has no contacts.
        return ''


class Event(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    event_type = models.ForeignKey(EventType, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, null=True, blank=True, on_delete=models.SET_NULL)
    other_user = models.ForeignKey(User,
                                   related_name='other_user',
                                   null=True,
                                   blank=True,
                                   on_delete=models.SET_NULL)
    call = models.ForeignKey(Call, null=True, blank=True, on_delete=models.SET_NULL)
    start = models.DateTimeField(null=True, blank=True)
    duration = models.IntegerField(null=True, blank=True)
    badge = models.ForeignKey(Badge, null=True, blank=True, on_delete=models.SET_NULL)
    tc = models.ForeignKey('TwilioCall', null=True, blank=True, on_delete=models.SET_NULL)
    tsms = models.ForeignKey('TwilioSMS', null=True, blank=True, on_delete=models.SET_NULL)
    cef = models.ForeignKey('ContactEventForm', null=True, blank=True, on_delete=models.SET_NULL)
    google_place = models.ForeignKey('GooglePlace',
                                     null=True,
                                     blank=True,
                                     on_delete=models.SET_NULL)
    created = models.DateTimeField()
    popular = models.DateTimeField()
    points = models.IntegerField(default=0)
    appointment = models.ForeignKey('Appointment', null=True, blank=True, on_delete=models.SET_NULL)
    followup = models.ForeignKey('Followup', null=True, blank=True, on_delete=models.SET_NULL)
    message = models.TextField(null=True, blank=True)
    video_message = models.ForeignKey('VideoMessage', null=True, blank=True,on_delete=models.SET_NULL)

    def __str__(self):
        return '%s %s %s' % (self.user.first_name, self.user.last_name, self.event_type.name)

    def get_created(self):
        import time
        return int(time.mktime(self.created.timetuple()))

    def start_short(self):
        s = ''
        if self.start:
            s = self.start.strftime('%Y-%m-%d %H:%I:%S')
        return s

    def get_event_type_points(self):
        return EventTypePoint.objects.filter(event_type=self.event_type_id)

    def comments_count(self):
        try:
            c = EventComment.objects.filter(event=self.id).count()
        except:
            c = 0
        return c

    def likes_count(self):
        return EventLike.objects.filter(event=self.id).count()

    def get_comments(self):
        return self.eventcomment_set.order_by('created').all()

    def event_length(self):
        hours = 0
        minutes = 0
        try:
            duration = int(self.duration)
        except:
            duration = 0
        if duration > 3600:
            hours = duration // 3600
            minutes = duration % 3600 // 60
            seconds = duration - (hours * 3600) - (minutes * 60)
        elif duration > 60:
            minutes = duration // 60
            seconds = duration - (minutes * 60)
        else:
            seconds = duration
        hours = "{0:02d}".format(hours)
        minutes = "{0:02d}".format(minutes)
        seconds = "{0:02d}".format(seconds)
        if hours == '00':
            return "%s:%s" % (minutes, seconds)
        else:
            return "%s:%s:%s" % (hours, minutes, seconds)

    def event_personnels(self):
        personnels = []
        if self.call:
            if self.call.contact_phone:
                pers = self.call.contact_phone.get_personnels()
                for per in pers:
                    personnels.append(per)
        elif self.cef:
            personnels = self.cef.get_cef_personnel()
        elif self.appointment:
            personnels = self.appointment.personnels()
        elif self.followup:
            personnels = self.followup.personnels()
        elif self.tc:
            if self.tc.contact_phone:
                pers = self.tc.contact_phone.get_personnels()
                for per in pers:
                    personnels.append(per)
        return personnels

    def get_personnels(self):
        personnels = self.event_personnels()
        per_dtl = []
        for per in personnels:
            per_dtl.append(per.fullname())
        if len(per_dtl) > 4:
            pers = []
            for x in range(4):
                pers.append('%s' % per_dtl[x])
            return '<b> %s and %s others </b>' % (', '.join(pers), len(per_dtl) - 4)
        if per_dtl:
            return '<b> %s </b>' % (', '.join(per_dtl))
        return ''

    def get_report_data_list(self, **kwargs):
        try:
            rep = self.user.userprofile.fullname()
        except:
            rep = ''
        try:
            dsc = self.event_type.desc
        except:
            dsc = ''
        if not self.company.people_tab:
            try:
                cnct = self.contact.fullname()
            except:
                cnct = ''
        else:
            cnct = ''
            try:
                personnels = self.event_personnels()
                for per in personnels:
                    try:
                        cnct += per.fullname() + ','
                    except:
                        pass
                cnct = cnct.strip(',')
            except:
                pass

        try:
            cnct_cmp = self.contact.contact_company.name
        except:
            cnct_cmp = ''
        try:
            st = timezone.localtime(self.start)
            st = st.strftime(settings.CSV_TIME_FORMAT)
        except:
            st = ''
        try:
            oth = self.other_user.userprofile.fullname()
        except:
            oth = ''
        try:
            ef = self.cef.event_form.name
        except:
            ef = ''
        try:
            if self.duration and self.duration > 0:
                el = self.event_length()
            else:
                el = ''
        except:
            el = ''
        try:
            etpv = ''
            for etp in self.get_event_type_points():
                if etp.point.value > 0:
                    etpv = etp.point.value
        except:
            etpv = ''

        data = [rep, dsc, cnct, cnct_cmp, oth, st, el, etpv, ef]

        if self.company.id in [6177, 26]:
            call_rep_name = ''
            call_type = ''
            call_rating = ''
            call_evelution = ''
            try:
                twilio_log('event twilio call report data')
                tc = TwilioCall.objects.filter(id=self.tc_id)[0]
            except:
                tc = None

            if tc:
                if tc.user:
                    call_rep_name = tc.user.userprofile.fullname()

                if tc.call_type_id in [1, 2]:
                    call_type = 'Outbound'
                else:
                    call_type = 'Inbound'

                if tc.call_evaluation_id:
                    call_evelution = tc.call_evaluation.name

                if tc.rating:
                    call_rating = str(tc.rating) + ' star'

            data.extend([call_rating, call_type, call_rep_name, call_evelution])

        return data


class EventComment(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    event = models.ForeignKey(Event, on_delete=models.CASCADE)
    comment = models.CharField(max_length=1024)
    created = models.DateTimeField()

    def __str__(self):
        return '%s %s %s' % (self.user.first_name, self.user.last_name, self.created)

    def likes_count(self):
        return EventCommentLike.objects.filter(comment=self.id).count()


class EventLike(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    event = models.ForeignKey(Event, on_delete=models.CASCADE)

    def __str__(self):
        return '%s %s %s' % (self.user.first_name, self.user.last_name, self.event.event_type.name)


class EventCommentLike(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    event_comment = models.ForeignKey(EventComment, on_delete=models.CASCADE)

    def __str__(self):
        return '%s %s %s' % (self.user.first_name,
                             self.user.last_name,
                             self.event_comment.event.event_type.name)


class Webinar(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    event_form = models.ForeignKey('EventForm', on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    created = models.DateTimeField()
    duration = models.IntegerField(null=True, blank=True, default=0)


class Appointment(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    start = models.DateTimeField()
    stop = models.DateTimeField(null=True, blank=True)
    latitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    longitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    apt_end_latitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    apt_end_longitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    duration = models.IntegerField(null=True, blank=True, default=0)
    notes = models.TextField()
    title = models.CharField(max_length=1024, null=True, blank=True)
    address = models.CharField(max_length=1024, null=True, blank=True)
    scheduled = models.BooleanField(default=False)
    item_id = models.CharField(max_length=48, null=True, blank=True)
    html_link = models.CharField(max_length=255, null=True, blank=True)
    event_form = models.ForeignKey('EventForm', on_delete=models.CASCADE)
    updated = models.DateTimeField()
    created = models.DateTimeField()
    started_with_plus = models.BooleanField(default=False)
    ended_with_plus = models.BooleanField(default=False)

    def to_hash(self):
        try:
            if self.created:
                self.created = timezone.localtime(self.created, timezone.get_current_timezone())
            created = self.created.strftime('%Y-%m-%d %H:%M:%S')
        except:
            created = ''

        try:
            if self.created:
                self.updated = timezone.localtime(self.updated, timezone.get_current_timezone())
            updated = self.updated.strftime('%Y-%m-%d %H:%M:%S')
        except:
            updated = ''

        try:
            if self.start:
                self.start = timezone.localtime(self.start, timezone.get_current_timezone())
            start = self.start.strftime('%Y-%m-%d %H:%M:%S')
        except:
            start = ''

        try:
            if self.stop:
                self.stop = timezone.localtime(self.stop, timezone.get_current_timezone())
            stop = self.stop.strftime('%Y-%m-%d %H:%M:%S')
        except:
            stop = ''

        try:
            rep = self.user.userprofile.fullname()
        except:
            rep = ''

        try:
            rep_email = self.user.email
        except:
            rep_email = ''

        scheduled = '1' if self.scheduled else '0'

        try:
            miles_away = float(self.miles_away())
        except:
            miles_away = ''

        try:
            latitude = str(self.latitude)
        except:
            latitude = ''

        try:
            longitude = str(self.longitude)
        except:
            longitude = ''

        data = {'id': self.id,
                'rep_id': self.user_id,
                'rep': rep,
                'rep_email': rep_email,
                'contact_id': self.contact_id,
                'contact': self.contact.fullname(),
                'start': start,
                'stop': stop,
                'updated': updated,
                'created': created,
                'latitude': latitude,
                'longitude': longitude,
                'distance': miles_away,
                'duration': self.duration,
                'notes': self.notes,
                'title': self.title,
                'address': self.address,
                'scheduled': scheduled,
                }

        return data

    def auto_end(self):
        self.updated = timezone.localtime(timezone.now())
        self.duration = 1800
        self.save()

        try:
            up = self.user.userprofile
        except:
            up = None

        if up:
            up.add_event(name='mobile_appointment_checkout',
                         contact=self.contact,
                         start=self.start,
                         duration=self.duration,
                         appointment=self)

    def miles_away(self):
        d = calc_distance(self.latitude,
                          self.longitude,
                          self.contact.latitude,
                          self.contact.longitude)
        if d:
            return '%0.1f' % d
        return ''

    def apt_miles_away(self):
        distance = calc_distance(self.apt_end_latitude,
                                 self.apt_end_longitude,
                                 self.contact.latitude,
                                 self.contact.longitude)
        if distance:
            return '%0.1f' % distance
        return ''

    def too_far_away(self):
        d = calc_distance(self.latitude,
                          self.longitude,
                          self.contact.latitude,
                          self.contact.longitude)
        if d:
            return d and d > 0.5
        return False

    def apt_end_too_far_away(self):
        """
        Function to calculate the distance between the appointments end and contact location
        return: Return boolean indicates the appointment is virtual or direct
        """
		
        distance = calc_distance(self.apt_end_latitude,
                                 self.apt_end_longitude,
                                 self.contact.latitude,
                                 self.contact.longitude)
        if distance:
            return distance and distance > 0.5
        return False

    def started_five_miles_away(self):
        """
        Function to calculate the distance between the appointments start and contact location
        @return: Return boolean indicates the appointment is virtual or direct
        """

        distance_in_miles = calc_distance(self.latitude,
                                          self.longitude,
                                          self.contact.latitude,
                                          self.contact.longitude)
        if distance_in_miles:
            return distance_in_miles and distance_in_miles > 5
        return False

    def get_m_title(self):
        contact = self.contact
        name = ('%s %s' % (contact.first_name, contact.last_name)).strip()
        if len(name) == 0:
            name = contact.contact_company.name.strip()
        url = ''
        try:
            im = get_thumbnail(contact.image, '48x48', crop='center')
        except:
            im = None
        if im:
            url = '%s' % im.url
        else:
            url = ''
        if url == '':
            try:
                im = get_thumbnail(contact.contact_type.image, '48x48', crop='center')
            except:
                im = None
            if im:
                url = '%s' % im.url
            else:
                url = ''

        if self.scheduled:
            return '%s|%s|%s|%s' % (contact.id, name, url, self.id)
        else:
            return '%s|%s|%s' % (contact.id, name, url)

    def m_appt_reminders_list(self):
        from appointments.templatetags.appointments_extras import appt_reminders_list
        return appt_reminders_list(self, m=True)

    def m_appt_invites_list(self):
        from appointments.templatetags.appointments_extras import appt_invites_list
        return appt_invites_list(self, m=True)

    def personnels(self):
        return AppointmentPersonnel.objects.filter(appointment=self)

    def add_cal_event(self, ugc):
        now = timezone.localtime(timezone.now())
        at = AccessToken.objects.filter(user=self.user, expires__gte=now).first()
        if at is None:
            rt = RefreshToken.objects.filter(user=self.user).first()
            if rt:
                at = rt.get_new_access_token()

        if at:
            try:
                validate_google_calendar(at.token, ugc)
            except:
                logger.error("Google Calendar Sync Error while validating ugc, UGC id: %s", ugc,
                             exc_info=sys.exc_info())
            userTimezone = self.user.userprofile.get_user_timezone()
            event = {
                'summary': self.title,
                'location': self.address,
                'start': {
                    'dateTime': self.start.strftime('%Y-%m-%dT%H:%M:00'),
                    'timeZone': userTimezone
                },
                'end': {
                    'dateTime': self.stop.strftime('%Y-%m-%dT%H:%M:00'),
                    'timeZone': userTimezone
                },
                'attendees': [],
                'reminders': {'useDefault': 'false', 'overrides': []},
                'sendNotifications': 'true'
            }

            for i in self.invites():
                event['attendees'].append({'email': i.email})

            for r in self.reminders():
                event['reminders']['overrides'].append({'method': r.reminder_type.name,
                                                        'minutes': r.minutes()})

            data = json.dumps(event)

            h = http.client.HTTPSConnection('www.googleapis.com')

            headers = {"Content-type": "application/json",
                       "Authorization": "Bearer %s" % at.token, }

            path = '/calendar/v3/calendars/%s/events' % ugc.item_id

            h.request('POST', path, data, headers)
            r = h.getresponse()

            try:
                result = r.read().strip()
            except:
                logger.error("Google Cal Appointment Sync. Error in getting response, Id: %s, Response: %s",
                             self.id, r, exc_info=sys.exc_info())
                result = None

            if result:
                try:
                    a = json.loads(result)
                except:
                    logger.error("Google Cal Appointment Sync. Error in parsing response, Id: %s, Response: %s",
                                 self.id, result, exc_info=sys.exc_info())
                    a = None

                if a:
                    try:
                        item_id = a['id']
                    except:
                        logger.error("Google Cal Appointment Sync. Error in getting item_id, Id: %s, Response: %s",
                                     self.id, a, exc_info=sys.exc_info())
                        item_id = None

                    try:
                        html_link = a['htmlLink']
                    except:
                        logger.error("Google Cal Appointment Sync. Error in getting html_link, Id: %s, Response: %s",
                                     self.id, a, exc_info=sys.exc_info())
                        html_link = None

                    self.item_id = item_id
                    self.html_link = html_link
                    self.save()

    def update_cal_event(self, ugc):
        now = timezone.localtime(timezone.now())
        at = AccessToken.objects.filter(user=self.user, expires__gte=now).first()
        if at is None:
            rt = RefreshToken.objects.filter(user=self.user).first()
            if rt:
                at = rt.get_new_access_token()

        if at:
            try:
                validate_google_calendar(at.token, ugc)
            except:
                logger.error("Google Calendar Sync Error while validating ugc, UGC id: %s", ugc,
                             exc_info=sys.exc_info())
            userTimezone = self.user.userprofile.get_user_timezone()
            event = {
                'summary': self.title,
                'location': self.address,
                'start': {
                    'dateTime': self.start.strftime('%Y-%m-%dT%H:%M:00'),
                    'timeZone': userTimezone
                },
                'end': {
                    'dateTime': self.stop.strftime('%Y-%m-%dT%H:%M:00'),
                    'timeZone': userTimezone
                },
                'attendees': [],
                'reminders': {'useDefault': 'false', 'overrides': []},
                'sendNotifications': 'true'
            }

            for i in self.invites():
                event['attendees'].append({'email': i.email})

            for r in self.reminders():
                event['reminders']['overrides'].append({'method': r.reminder_type.name,
                                                        'minutes': r.minutes()})

            data = json.dumps(event)

            h = http.client.HTTPSConnection('www.googleapis.com')

            headers = {"Content-type": "application/json",
                       "Authorization": "Bearer %s" % at.token}

            path = '/calendar/v3/calendars/%s/events/%s' % (ugc.item_id, self.item_id)

            h.request('PUT', path, data, headers)
            r = h.getresponse()

            try:
                result = r.read().strip()
            except:
                logger.error("Google Cal Appointment update Sync. "
                             "Error in getting response, Id: %s, Response: %s",
                             self.id, r, exc_info=sys.exc_info())
                result = None

            if result:
                try:
                    a = json.loads(result)
                except:
                    logger.error("Google Cal Appointment update Sync. "
                                 "Error in parsing response, Id: %s, Response: %s",
                                 self.id, result, exc_info=sys.exc_info())
                    a = None

                if a:
                    try:
                        item_id = a['id']
                    except:
                        logger.error(
                            "Google Cal Appointment update Sync. "
                            "Error in getting item_id, Id: %s, Response: %s",
                            self.id, a, exc_info=sys.exc_info())
                        item_id = None

                    try:
                        html_link = a['htmlLink']
                    except:
                        logger.error("Google Cal Appointment Sync. "
                                     "Error in getting html_link, Id: %s, Response: %s",
                                     self.id, a, exc_info=sys.exc_info())
                        html_link = None

                    self.item_id = item_id
                    self.html_link = html_link
                    self.save()

    def reminders(self):
        return AppointmentReminder.objects.filter(appointment=self)

    def invites(self):
        return AppointmentInvite.objects.filter(appointment=self)

    def has_followup(self):
        followup = Followup.objects.filter(appointment=self).first()
        return True if followup else False

    def followup_date(self):
        followup = Followup.objects.filter(appointment=self).first()
        return followup.start

    def __str__(self):
        return '%s %s %s %s' % (self.user.first_name, self.user.last_name, self.start, self.contact)

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))

    def formatted_start(self):
        return '%s' % timezone.localtime(self.start,
                                         timezone.get_current_timezone()) \
            .strftime('%Y-%m-%d %H:%M:%S')

    def start_time(self):
        return '%s%s' % (int(self.start.strftime('%I')), self.start.strftime(':%M%P').lower())

    def rep_start_time(self):
        user_timezone = self.user.userprofile.get_user_timezone()
        user_tz = pytz.timezone(user_timezone)
        if user_tz is not None:
            masked_start_time = timezone.localtime(self.start, user_tz)
        else:
            masked_start_time = self.start

        return '%s%s' % (int(masked_start_time.strftime('%I')),
                         masked_start_time.strftime(':%M%P').lower())

    def appointment_length(self):
        return get_duration_time(self.duration)

    def get_appt_event_form_link(self):
        cef = ContactEventForm.objects.filter(appointment=self).first()
        if cef:
            link = "/eforms/%s/edit/%s/" % (cef.event_form_id, cef.id)
        else:
            link = "/eforms/entries/"
        return link

    def get_report_data_list(self, **kwargs):
        data = [
            self.contact.contact_company.name,
            self.start.strftime(settings.CSV_TIME_FORMAT),
            self.duration,
            self.notes,
            self.title or '',
            self.address or '',
            self.created.strftime(settings.CSV_TIME_FORMAT),
            self.updated.strftime(settings.CSV_TIME_FORMAT)
        ]
        contact_details = get_contact_details_for_export(self.contact, True, True, **kwargs)
        data.extend(contact_details[1:])
        return data


class DurationType(models.Model):
    name = models.CharField(max_length=32)


class HustleSetting(models.Model):
    user = models.IntegerField(null=True, blank=True)
    contacts_not_contacted_days = models.IntegerField(null=True, blank=True, default=21)
    followup_work_days = models.IntegerField(null=True, blank=True, default=21)
    reward_cycle = models.IntegerField(null=True, blank=True, default=0)
    opportunity_card_percent = models.IntegerField(null=True, blank=True, default=25)
    past_appointments_card_percent = models.IntegerField(null=True, blank=True, default=25)
    followup_card_percent = models.IntegerField(null=True, blank=True, default=25)
    not_contacted_card_percent = models.IntegerField(null=True, blank=True, default=25)
    rewards = models.IntegerField(null=True, blank=True, default=25)

    contacts_not_contacted = models.BooleanField(default=False)
    followup_show = models.BooleanField(default=False)
    reward_screen = models.BooleanField(default=False)
    reward_screen_opportunity = models.BooleanField(default=False)
    reward_screen_past_appointments = models.BooleanField(default=False)
    reward_screen_followups = models.BooleanField(default=False)
    reward_screen_contacts = models.BooleanField(default=False)


class HustleManagerSetting(models.Model):
    user = models.IntegerField(null=True, blank=True)
    contacts_not_contacted_days = models.IntegerField(null=True, blank=True, default=21)
    followup_work_days = models.IntegerField(null=True, blank=True, default=21)
    reward_cycle = models.IntegerField(null=True, blank=True, default=0)
    opportunity_card_percent = models.IntegerField(null=True, blank=True, default=25)
    past_appointments_card_percent = models.IntegerField(null=True, blank=True, default=25)
    followup_card_percent = models.IntegerField(null=True, blank=True, default=25)
    not_contacted_card_percent = models.IntegerField(null=True, blank=True, default=25)
    rewards = models.IntegerField(null=True, blank=True, default=25)

    contacts_not_contacted = models.BooleanField(default=False)
    followup_show = models.BooleanField(default=False)
    reward_screen = models.BooleanField(default=False)
    reward_screen_opportunity = models.BooleanField(default=False)
    reward_screen_past_appointments = models.BooleanField(default=False)
    reward_screen_followups = models.BooleanField(default=False)
    reward_screen_contacts = models.BooleanField(default=False)


class ReminderType(models.Model):
    name = models.CharField(max_length=32)


class AppointmentReminder(models.Model):
    appointment = models.ForeignKey(Appointment, on_delete=models.CASCADE)
    reminder_type = models.ForeignKey(ReminderType, on_delete=models.CASCADE)
    duration_type = models.ForeignKey(DurationType, on_delete=models.CASCADE)
    duration = models.IntegerField(default=0)

    def minutes(self):
        n = self.duration_type.name
        if n == 'weeks':
            return self.duration * 60 * 24 * 7
        elif n == 'days':
            return self.duration * 60 * 24
        elif n == 'hours':
            return self.duration * 60
        elif n == 'minutes':
            return self.duration
        return 0


class AppointmentInvite(models.Model):
    appointment = models.ForeignKey(Appointment, on_delete=models.CASCADE)
    email = models.CharField(max_length=64)


# contacts
class CFieldTable(models.Model):
    name = models.CharField(max_length=12)


# radio, text, select, etc.
class CFieldType(models.Model):
    name = models.CharField(max_length=12)

    def get_name(self):
        n = self.name.replace('_', ' ')
        return n.title()

    def is_auto(self):
        return self.name.find('auto') > -1


# regular fields
class RField(models.Model):
    name = models.CharField(max_length=64)

    def pretty_name(self):
        n = self.name
        return '%s' % n.replace('_id', '').replace('_', ' ').title()


# a single custom field owned by a company
class CField(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    cfield_table = models.ForeignKey(CFieldTable, on_delete=models.CASCADE)
    cfield_type = models.ForeignKey(CFieldType, null=True, blank=True, on_delete=models.SET_NULL)
    cfield_option_default = models.ForeignKey('CFieldOption',
                                              on_delete=models.SET_NULL,
                                              null=True,
                                              blank=True,
                                              related_name='cfield_cfield_option_default')
    rfield = models.ForeignKey(RField, null=True, blank=True, on_delete=models.SET_NULL)
    cfield = models.ForeignKey('CField', null=True,
                               blank=True,
                               related_name='cfield_cfield',
                               on_delete=models.CASCADE)
    position = models.IntegerField()
    points = models.IntegerField(default=0)
    hide_on_checkout = models.BooleanField(default=False)
    required = models.BooleanField(default=False)
    lock = models.BooleanField(default=False)

    def is_auto(self):
        return True if (self.cfield_type and self.cfield_type.is_auto()) else False

    def to_hash(self):
        try:
            cfield_option_default = self.cfield_option_default.name
        except:
            cfield_option_default = ''

        try:
            rfield = self.rfield.name
        except:
            rfield = ''

        try:
            cfield = self.cfield.name
        except:
            cfield = ''

        try:
            cfield_table = self.cfield_table.name
        except:
            cfield_table = ''

        options = []
        for cfo in CFieldOption.objects.filter(cfield=self):
            options.append(cfo.to_hash())

        data = {
            'id': self.id,
            'name': self.name,
            'cfield_table': cfield_table,
            'cfield_type': self.cfield_type.name if self.cfield_type else '',
            'cfield_option_default': cfield_option_default,
            'rfield': rfield,
            'cfield': cfield,
            'position': self.position,
            'points': self.points,
            'hide_on_checkout': '1' if self.hide_on_checkout else '0',
            'options': options,
        }

        return data


class EventFormTreatAs(models.Model):
    name = models.CharField(max_length=50)


class EventForm(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=32)
    position = models.IntegerField()
    post_back_url = models.CharField(max_length=255, null=True, blank=True)
    post_back_secret = models.CharField(max_length=64, null=True, blank=True)
    post_back_method = models.IntegerField(null=True, blank=True)
    points = models.IntegerField(default=0)
    is_schedule_followup = models.BooleanField(default=False)
    send_email_to_rep = models.BooleanField(default=False)
    event_form_treat_as = models.ForeignKey(EventFormTreatAs, null=True, on_delete=models.SET_NULL)
    prefill_data = models.BooleanField(default=True)
    is_after_call_form = models.BooleanField(default=False)
    hide = models.BooleanField(default=False)
    is_clickable = models.BooleanField(default=True)


    def __str__(self):
        return '%s' % self.name

    def has_image_field(self):
        for efcf in EventFormCField.objects.filter(event_form=self):
            try:
                cft = efcf.cfield.cfield_type
            except:
                cft = None
            if cft and cft.name == 'image':
                return True
            try:
                cft = efcf.cfield.cfield.cfield_type
            except:
                cft = None
            if cft and cft.name == 'image':
                return True
        return False

    def notifications(self):
        emails = ''
        for efe in EventFormEMail.objects.filter(event_form=self):
            emails += '%s\n' % efe.email
        return emails

    def notifications_html(self):
        emails = ''
        for efe in EventFormEMail.objects.filter(event_form=self):
            emails += '%s<br />' % efe.email
        return emails

    def get_entries(self):
        return ContactEventForm.objects.filter(company=self.company,
                                               event_form=self).order_by('-created')

    def entries_count(self):
        count = ContactEventForm.objects.filter(company=self.company,
                                                event_form=self).aggregate(Count('id'))['id__count']
        if count is None:
            return 0
        return count

    def cfield_ids_count(self):
        return len(self.cfield_ids())

    def cfield_ids(self):
        return [str(_.cfield_id)
                for _ in EventFormCField.objects.filter(event_form=self).order_by('position')
                if not (_.cfield.company.people_tab and _.cfield and _.cfield.rfield and
                        (_.cfield.rfield.name == 'first_name' or _.cfield.rfield.name == 'last_name'))
                ]

    def get_cfields(self, show_hidden=True, show_img_fields=True):
        cfields = []
        image = CFieldType.objects.filter(name='image')[:1][0]

        for efc in EventFormCField.objects.filter(event_form=self).order_by('position'):
            cf = efc.cfield
            try:
                if cf.company.people_tab and \
                        (cf.rfield.name == 'first_name' or cf.rfield.name == 'last_name'):
                    continue
            except:
                pass

            cfe = None
            if cf.cfield:
                cfe = cf.cfield
            if not cf.cfield and not cf.rfield and not cf.cfield_type:
                continue
            if show_hidden:
                if cf.cfield_type == image or (cfe and cfe.cfield_type == image):
                    if show_img_fields:
                        cfields.append(cf)
                else:
                    cfields.append(cf)
            else:
                cfa = CFieldAuto.objects.filter(company=self.company, cfield=cf).first()
                if not (cfa and cfa.hide):
                    if cf.cfield_type == image or (cfe and cfe.cfield_type == image):
                        if show_img_fields:
                            cfields.append(cf)
                    else:
                        cfields.append(cf)

        return cfields

    def get_rfield_ids(self):
        cfield_ids = EventFormCField.objects \
            .filter(event_form=self,
                    cfield__rfield__isnull=False) \
            .values_list('cfield__rfield_id', flat=True)
        return list(cfield_ids)

    def get_ccfield_ids(self):
        cfield_ids = EventFormCField.objects \
            .filter(event_form=self,
                    cfield__cfield__isnull=False) \
            .values_list('cfield__cfield_id', flat=True)
        return list(cfield_ids)

    def next_cfield_position(self):
        efcf = EventFormCField.objects.filter(event_form=self).order_by('-position').first()
        return efcf.position + 1 if efcf else 0


class EventFormContactType(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    event_form = models.ForeignKey(EventForm, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, on_delete=models.CASCADE)


class EventFormPostBackLog(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    event_form = models.ForeignKey(EventForm, on_delete=models.CASCADE)
    url = models.CharField(max_length=255)
    method = models.IntegerField()
    status = models.IntegerField()
    reason = models.CharField(max_length=64)
    request = models.CharField(max_length=4096, null=True, blank=True)
    response = models.CharField(max_length=4096, null=True, blank=True)
    created = models.DateTimeField()


class EventFormCField(models.Model):
    event_form = models.ForeignKey(EventForm, on_delete=models.CASCADE)
    cfield = models.ForeignKey(CField, on_delete=models.CASCADE)
    position = models.IntegerField()


class OppFormCField(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    cfield = models.ForeignKey(CField, on_delete=models.CASCADE)
    position = models.IntegerField()


class ContactEventForm(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    event_form = models.ForeignKey(EventForm, on_delete=models.CASCADE)
    created = models.DateTimeField()
    points = models.IntegerField(default=0)
    latitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    longitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    completed = models.NullBooleanField(default=False)
    completed_date = models.DateTimeField(null=True, blank=True)
    appointment = models.ForeignKey(Appointment, on_delete=models.SET_NULL, null=True)

    def get_report_data_list(self, **kwargs):
        data = [
            self.contact.contact_company.name,
            self.event_form.name,
            self.points,
            self.created.strftime(settings.CSV_TIME_FORMAT),
            self.completed_date if self.completed else 'No'
        ]
        contact_details = get_contact_details_for_export(self.contact, True, True, **kwargs)
        data.extend(contact_details[1:])

        return data

    def to_hash(self):
        self.created = timezone.localtime(self.created, timezone.get_current_timezone())

        data = {
            'contact_event_form_id': self.id,
            'rep': self.user.userprofile.to_hash(),
            'contact_id': self.contact_id,
            'contact_name': self.contact.fullname(),
            'contact_full_addres': self.contact.full_address(),
            'contact_company_name': self.contact.company.name if self.contact.company else '',
            'event_form_id': self.event_form_id,
            'event_form_name': self.event_form.name,
            'completed': '1' if self.completed else '0',
            'created': self.created.strftime('%Y-%m-%d %H:%M:%S')
        }

        return data

    def image_cfield_ids(self, skip_lock=False):
        cfields = [str(self.id)]
        image = CFieldType.objects.filter(name='image')[:1][0]

        for efc in EventFormCField.objects.filter(event_form=self.event_form).order_by('position'):
            if efc.cfield.cfield:
                cf = efc.cfield.cfield
            else:
                cf = efc.cfield
            if skip_lock and cf.lock:
                continue
            if cf.cfield_type == image:
                cfields.append(str(cf.id))
        return cfields

    def map_link(self):
        try:
            lat = self.latitude
        except:
            lat = None

        try:
            lon = self.longitude
        except:
            lon = None

        if lat and lon:
            href = 'http://maps.google.com/?q=%s,%s' % (lat, lon)
            return '%s,%s <a href="%s" target="_blank" rel="noopener noreferrer">Google Map</a>' % \
                   (lat, lon, href)

        return '&nbsp;'

    def miles_away(self):
        d = calc_distance(self.latitude,
                          self.longitude,
                          self.contact.latitude,
                          self.contact.longitude)
        if d:
            return '%0.1f' % d
        return ''

    def cef_apt_miles_away(self):
        distance = calc_distance(self.appointment.apt_end_latitude,
                                 self.appointment.apt_end_longitude,
                                 self.contact.latitude,
                                 self.contact.longitude)
        if distance:
            return '%0.1f' % distance
        return ''

    def too_far_away(self):
        d = calc_distance(self.latitude,
                          self.longitude,
                          self.contact.latitude,
                          self.contact.longitude)
        if d:
            return d and d > 0.5
        return False

    def cef_apt_end_too_far_away(self):
        distance = calc_distance(self.appointment.apt_end_latitude,
                                 self.appointment.apt_end_longitude,
                                 self.contact.latitude,
                                 self.contact.longitude)
        if distance:
            return distance and distance > 0.5
        return False

    def get_cfields(self, show_hidden=True):
        return self.event_form.get_cfields(show_hidden=show_hidden)

    def award_points(self):
        select = CFieldType.objects.filter(name='select')[:1][0]
        radio = CFieldType.objects.filter(name='radio')[:1][0]
        checkbox = CFieldType.objects.filter(name='checkbox')[:1][0]

        p = self.event_form.points

        for efcf in EventFormCField.objects.filter(event_form=self.event_form):
            cfield = efcf.cfield
            cf = cfield
            if cfield.cfield:
                cf = cfield.cfield

            cfv = CFieldValue.objects.filter(entity_id=self.id, cfield=cf).first()

            if cfv and cfv.cf_value:
                if cfield.cfield_type_id in [select.id, radio.id]:
                    cfo = CFieldOption.objects.filter(cfield=cf, id=int(cfv.cf_value)).first()
                    if cfo:
                        p += cfo.points
                elif cf.cfield_type_id == checkbox.id:
                    if cfv.cf_value == '1':
                        p += cfield.points
                elif len(cfv.cf_value) != 0:
                    p += cfield.points

        self.points = p
        self.save()

        try:
            up = self.user.userprofile
        except:
            up = None

        if up and p != 0:
            up.rerank()

    def get_cef_personnel(self):
        pers = ContactEventFormPersonnel.objects \
            .filter(contacteventform=self) \
            .values('personnel_id')
        return ContactPersonnel.objects.filter(id__in=pers).order_by('-last_contacted')[:100]

    def get_scheduled_task(self):
        f = None
        if self.event_form.is_schedule_followup:
            f = Followup.objects.filter(contacteventform=self).first()
        return f

    def get_heads_up_notes(self):
        """
        Fetch the Contact Event Form Heads up notes.
        :return: Notes values or None.
        """
        from cfields.views import find_entity_heads_up_notes
        return find_entity_heads_up_notes(self)


class EventFormEMail(models.Model):
    event_form = models.ForeignKey(EventForm, on_delete=models.CASCADE)
    email = models.CharField(max_length=64)

    def __str__(self):
        return '%s %s' % (self.event_form.name, self.email)


class FollowupType(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    position = models.IntegerField()
    is_default = models.BooleanField(default=False)


def change_access_token(access_token):
    # Getting access token
    token = AccessToken.objects.filter(token=access_token).first()
    if token:
        # If access token to get RefreshToken user id
        refresh_token = RefreshToken.objects.filter(user=token.user).first()
        if refresh_token:
            access_token_new = refresh_token.get_new_access_token()
            access_token = access_token_new.token

    url = 'https://www.googleapis.com/calendar/v3/users/me/calendarList?access_token=%s' % access_token
    req = urllib.request.Request(url)
    opener = urllib.request.build_opener(urllib.request.HTTPSHandler(debuglevel=0))
    req = opener.open(req)
    return req


def validate_google_calendar(access_token, user_calendar):
    url = 'https://www.googleapis.com/calendar/v3/users/me/calendarList?access_token=%s' % access_token
    req = urllib.request.Request(url)
    opener = urllib.request.build_opener(urllib.request.HTTPSHandler(debuglevel=0))
    try:
        req = opener.open(req)
    except:
        # Getting New access token
        req = change_access_token(access_token)
    reply = req.read()
    req.close()
    a = json.loads(reply)

    primary_cal = None
    for i in a['items']:
        try:
            item_id = i['id']
        except:
            item_id = None

        if item_id == user_calendar.item_id:
            return True

        try:
            primary = True if i['primary'] == True else False
        except:
            primary = False

        if not primary:
            continue

        try:
            summary = i['summary']
        except:
            summary = None

        try:
            tz = i['timeZone'][:64]
        except:
            tz = None

        primary_cal = {'item_id': item_id, 'summary': summary, 'tz': tz}

    if primary_cal:
        ugc = UserGoogleCal.objects.filter(company=user_calendar.company,
                                           user=user_calendar.user,
                                           item_id=primary_cal['item_id'])[:1]
        try:
            ugc = ugc[0]
        except:
            ugc = UserGoogleCal(company=user_calendar.company,
                                user=user_calendar.user,
                                **primary_cal)
            ugc.save()

        user_calendar.user.userprofile.cal_followup = ugc
        user_calendar.user.userprofile.save()
        return True

    return False


class FollowupStage(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    fg_color = models.CharField(max_length=7)
    bg_color = models.CharField(max_length=7)
    position = models.IntegerField()
    map_with_not_completed = models.BooleanField(default=False)
    map_with_completed = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class FollowupPriority(models.Model):
    name = models.CharField(max_length=20)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class CalendarEventFollowups(models.Model):
    event_type = models.CharField(max_length=100, null=True, blank=True)
    range_type = models.CharField(max_length=100, null=True, blank=True)
    number_of_occurrences = models.IntegerField(null=True, blank=True)
    days_of_week = models.TextField(null=True, blank=True)
    days_of_month = models.IntegerField(null=True, blank=True)
    interval = models.IntegerField(null=True, blank=True)
    index = models.CharField(max_length=50, null=True, blank=True)
    start_date = models.DateTimeField(null=True, blank=True)
    end_date = models.DateTimeField(null=True, blank=True)
    month = models.IntegerField(null=True, blank=True)
    created = models.DateTimeField(null=True, blank=True)
    updated = models.DateTimeField(null=True, blank=True)


class Followup(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    start = models.DateTimeField()

    # stop = models.DateTimeField( null=True, blank=True )

    appointment = models.ForeignKey(Appointment,
                                    on_delete=models.SET_NULL,
                                    null=True,
                                    blank=True,
                                    related_name='followup_appointment')
    contacteventform = models.ForeignKey(ContactEventForm,
                                         on_delete=models.SET_NULL,
                                         null=True,
                                         blank=True,
                                         related_name='followup_contacteventform')
    duration = models.IntegerField(null=True, blank=True, default=0)
    notes = models.TextField()
    completed = models.NullBooleanField(null=True, blank=True)
    contact_phone = models.ForeignKey(ContactPhone,
                                      null=True,
                                      blank=True,
                                      on_delete=models.SET_NULL)

    send_google_cal = models.BooleanField(default=False)
    send_office_cal = models.BooleanField(default=False)
    item_id = models.CharField(max_length=48, null=True, blank=True)
    html_link = models.CharField(max_length=255, null=True, blank=True)
    office_item_id = models.TextField()
    office_html_link = models.TextField()

    updated = models.DateTimeField()
    created = models.DateTimeField()
    followup_type = models.ForeignKey(FollowupType,
                                      null=True,
                                      blank=True,
                                      on_delete=models.SET_NULL)
    stage = models.ForeignKey(FollowupStage,
                              null=True,
                              blank=True,
                              on_delete=models.SET_NULL)
    priority = models.ForeignKey(FollowupPriority,
                                 null=True,
                                 blank=True,
                                 on_delete=models.SET_NULL,
                                 default=3)
    calendar_event = models.ForeignKey(CalendarEventFollowups,
                                       null=True,
                                       blank=True,
                                       on_delete=models.CASCADE)


    def get_report_data_list(self, **kwargs):
        data = [
            self.contact.contact_company.name,
            self.start.strftime(settings.CSV_TIME_FORMAT),
            self.duration,
            self.notes,
            self.created.strftime(settings.CSV_TIME_FORMAT),
            self.updated.strftime(settings.CSV_TIME_FORMAT)
        ]
        contact_details = get_contact_details_for_export(self.contact, True, True, **kwargs)
        data.extend(contact_details[1:])

        return data

    def to_hash(self):
        try:
            rep = self.user.userprofile.to_hash()
        except:
            rep = {}
        return {
            'rep': rep,
            'contact_id': self.contact_id,
            'contact': self.contact.fullname(),
            'start_date': self.start.strftime('%Y-%m-%d %H:%M:%S'),
            'duration': self.duration / 60,
            'completed': '1' if self.completed else '0',
            'notes': self.notes,
            'id': self.id,
            'created': self.created.strftime('%Y-%m-%d %H:%M:%S'),
            'updated': self.updated.strftime('%Y-%m-%d %H:%M:%S')

        }

    def __str__(self):
        return '%s %s %s %s' % (self.user.first_name, self.user.last_name, self.start, self.contact)

    def get_contact_opps(self):
        return self.contact.get_opps()

    def get_contact_email_msgs(self):
        return self.contact.get_email_msgs()[:3]

    def get_contact_event_forms(self):
        return self.contact.get_contact_event_forms()[:3]

    def get_contact_notes(self):
        return self.contact.get_notes()[:3]

    def google_cal_summary(self):
        s = 'Followup-Up'
        try:
            s = self.followup_type.name if self.followup_type else 'Followup-Up'
        except:
            pass
        c_name = ''
        if self.contact.company.people_tab:
            pers = self.personnels()
            for per in pers:
                c_name = per.personnel.fullname()
        else:
            c_name = self.contact.fullname()

        if c_name:
            s += ' with %s' % c_name

        s += ' at %s' % self.contact.contact_company.name
        return s

    def push_cal_event(self):
        try:
            ugc = self.user.userprofile.cal_followup
        except Exception:
            ugc = None

        if ugc is None:
            # logger.error("Google Cal Followup Sync. Error in finding default calendar, Id: %s",
            #              self.id)
            return

        if self.item_id:
            self.result = self.update_cal_event(ugc)
            return self.result
        else:
            try:
                self.add_cal_event(ugc)
            except:
                logger.error("Google Cal Followup Sync. Error in adding event, Id: %s",
                             self.id, exc_info=sys.exc_info())

    def add_cal_event(self, ugc):
        pattern = None
        if self.calendar_event:
            from home.templatetags.home_extras import get_recurring_event_google_pattern
            pattern = get_recurring_event_google_pattern(self)

        if pattern != '' and pattern is not None:
            recurrence = [pattern]
        else:
            recurrence = []
        now = timezone.localtime(timezone.now())
        at = AccessToken.objects.filter(user=self.user, expires__gte=now).first()
        if at is None:
            rt = RefreshToken.objects.filter(user=self.user).first()
            if rt:
                at = rt.get_new_access_token()
        if at:
            try:
                validate_google_calendar(at.token, ugc)
            except:
                logger.error("Google Calendar Sync Error while validating ugc, UGC id: %s", ugc,
                             exc_info=sys.exc_info())

            end = self.start + timedelta(seconds=self.duration)
            c = self.contact

            from home.templatetags.home_extras import formatted_phone_number
            try:
                ph_number = formatted_phone_number(c.default_phone.phone_number)
            except:
                ph_number = ''
            try:
                cnt_cmp_name = c.contact_company.name
            except:
                cnt_cmp_name = ''
            c_name = ''
            try:
                if self.contact.company.people_tab:
                    pers = self.personnels()
                    for per in pers:
                        c_name = per.personnel.fullname()
                else:
                    c_name = c.fullname()
            except:
                pass

            desc = '''%s
                    %s
                    %s
                    %s
                    %s
                    Notes: %s
            ''' % (c_name, cnt_cmp_name, c.full_address(),
                   ph_number, c.email, self.notes)

            desc = desc.replace(' None ', ' ')
            userTimezone = self.user.userprofile.get_user_timezone()
            event = {
                'summary': self.google_cal_summary(),
                'description': desc,
                'location': '',
                'start': {
                    'dateTime': self.start.strftime('%Y-%m-%dT%H:%M:00'),
                    'timeZone': userTimezone
                },
                'end': {
                    'dateTime': end.strftime('%Y-%m-%dT%H:%M:00'),
                    'timeZone': userTimezone
                },
                'recurrence': recurrence,
                'attendees': [],
                'reminders': {'useDefault': 'false', 'overrides': []},
                'sendNotifications': 'true'
            }

            data = json.dumps(event)

            h = http.client.HTTPSConnection('www.googleapis.com')

            headers = {
                "Content-type": "application/json",
                "Authorization": "Bearer %s" % at.token
            }

            path = '/calendar/v3/calendars/%s/events' % ugc.item_id

            h.request('POST', path, data, headers)
            r = h.getresponse()

            try:
                result = r.read().strip()
            except:
                logger.error("Google Cal Followup Sync. "
                             "Error in getting response, Id: %s, Response: %s",
                             self.id, r, exc_info=sys.exc_info())
                result = None

            if result:
                try:
                    a = json.loads(result)
                except:
                    logger.error("Google Cal Followup Sync. "
                                 "Error in parsing response, Id: %s, Response: %s",
                                 self.id, result, exc_info=sys.exc_info())
                    a = None

                if a:
                    try:
                        item_id = a['id']
                    except:
                        logger.error("Google Cal Followup Sync. "
                                     "Error in getting item_id, Id: %s, Response: %s",
                                     self.id, a, exc_info=sys.exc_info())
                        item_id = None

                    try:
                        html_link = a['htmlLink']
                    except:
                        logger.error("Google Cal Followup Sync. "
                                     "Error in getting html_link, Id: %s, Response: %s",
                                     self.id, a, exc_info=sys.exc_info())
                        html_link = None

                    self.item_id = item_id
                    self.html_link = html_link
                    self.save()

    def update_cal_event(self, ugc):
        now = timezone.localtime(timezone.now())
        at = AccessToken.objects.filter(user=self.user, expires__gte=now).first()
        if at is None:
            rt = RefreshToken.objects.filter(user=self.user).first()
            if rt:
                at = rt.get_new_access_token()

        if at:
            try:
                validate_google_calendar(at.token, ugc)
            except:
                logger.error("Google Calendar Sync Error while validating ugc, UGC id: %s", ugc,
                             exc_info=sys.exc_info())

            end = self.start + timedelta(seconds=self.duration)
            c = self.contact
			
            pattern = None
            if self.calendar_event:
                from home.templatetags.home_extras import get_recurring_event_google_pattern
                pattern = get_recurring_event_google_pattern(self)

            if pattern != '' and pattern is not None:
                recurrence = [pattern]
            else :
                recurrence = []
        
            from home.templatetags.home_extras import formatted_phone_number
            try:
                ph_number = formatted_phone_number(c.default_phone.phone_number)
            except:
                ph_number = ''
            try:
                cnt_cmp_name = c.contact_company.name
            except:
                cnt_cmp_name = ''
            c_name = ''
            try:
                if self.contact.company.people_tab:
                    pers = self.personnels()
                    for per in pers:
                        c_name = per.personnel.fullname()
                else:
                    c_name = c.fullname()
            except:
                pass
            desc = '''%s
                        %s
                        %s
                        %s
                        %s
                        Notes: %s
            ''' % (c_name, cnt_cmp_name, c.full_address(),
                   ph_number, c.email, self.notes)

            desc = desc.replace(' None ', ' ')
            userTimezone = self.user.userprofile.get_user_timezone()
            event = {
                'summary': self.google_cal_summary(),
                'description': desc,
                'location': '',
                'start': {
                    'dateTime': self.start.strftime('%Y-%m-%dT%H:%M:00'),
                    'timeZone': userTimezone
                },
                'end': {
                    'dateTime': end.strftime('%Y-%m-%dT%H:%M:00'),
                    'timeZone': userTimezone
                },
                'recurrence' : recurrence,
                'attendees': [],
                'reminders': {'useDefault': 'false', 'overrides': []},
                'sendNotifications': 'true'
            }

            data = json.dumps(event)

            h = http.client.HTTPSConnection('www.googleapis.com')

            headers = {
                "Content-type": "application/json",
                "Authorization": "Bearer %s" % at.token
            }

            path = '/calendar/v3/calendars/%s/events/%s' % (ugc.item_id, self.item_id)

            h.request('PUT', path, data, headers)
            r = h.getresponse()

            try:
                result = r.read().strip()
            except Exception:
                logger.error("Google Cal Followup update Sync. "
                             "Error in getting response, Id: %s, Response: %s",
                             self.id, r, exc_info=sys.exc_info())
                result = None

            if result:
                try:
                    a = json.loads(result)
                except:
                    logger.error("Google Cal Followup update Sync. "
                                 "Error in parsing response, Id: %s, Response: %s",
                                 self.id, result, exc_info=sys.exc_info())
                    a = None
                if a and 'error' in a.keys():
                    self.item_id = None
                    self.html_link = None
                    self.save()
                    return 'redirect'
                else:
                    self.item_id = a['id']
                    self.html_link = a['htmlLink']
                    self.save()

    def push_office_cal_event(self):
        try:
            uoc = self.user.userprofile.office_cal_followup
        except:
            uoc = None

        if uoc is None:
            return

        if self.office_item_id:
            self.result = self.update_office_cal_event(uoc)
            return self.result
        else:
            self.add_office_cal_event(uoc)

    def add_office_cal_event(self, uoc):
        calendar_id  = self.calendar_event
        pattern = None
        range_info =  None

        if calendar_id is not None:
            from home.templatetags.home_extras import get_recurring_event_office_pattern
            pattern, range_info = get_recurring_event_office_pattern(self)
            
        from appointments.views import get_office_token
        oat = get_office_token(self.user)
        end = self.start + timedelta(seconds=self.duration)
        c = self.contact

        from home.templatetags.home_extras import formatted_phone_number
        from em.officeservice import create_event
        try:
            ph_number = formatted_phone_number(c.default_phone.phone_number)
        except:
            ph_number = ''
        try:
            cnt_cmp_name = c.contact_company.name
        except:
            cnt_cmp_name = ''
        c_name = ''
        try:
            if self.contact.company.people_tab:
                pers = self.personnels()
                for per in pers:
                    c_name = per.personnel.fullname()
            else:
                c_name = c.fullname()
        except:
            pass

        desc = '''<p><strong>%s</strong></p><p><strong>%s</strong></p><p>%s</p><p>%s</p><p>%s</p><p>Notes: %s</p>
                ''' % (c_name, cnt_cmp_name, c.full_address(), ph_number, c.email, self.notes)

        # - create event in Office 365
        userTimezone = self.user.userprofile.get_user_timezone()
        params = {
            'subject': self.google_cal_summary(),
            'body': {
                'contentType': 'HTML',
                'content': desc,
            },
            'start': {
                'dateTime': self.start.strftime('%Y-%m-%dT%H:%M:00'),
                'timeZone': userTimezone
            },
            "end": {
                'dateTime': end.strftime('%Y-%m-%dT%H:%M:00'),
                'timeZone': userTimezone
            },
        }
        if pattern is not None and range_info is not None :
            params['recurrence'] = {'pattern': pattern , 'range': range_info}
        res = create_event(oat.token, uoc.item_id, params)
        # - save response
        try:
            item_id = res['id']
        except Exception:
            item_id = None
        if item_id:
            self.office_item_id = item_id
            try:
                self.office_html_link = res['webLink']
            except Exception:
                pass
            self.save()

    def update_office_cal_event(self, uoc):
        # - get token
        from appointments.views import get_office_token
        oat = get_office_token(self.user)
        pattern = None
        range_info = None

        if self.calendar_event is not None:
            from home.templatetags.home_extras import get_recurring_event_office_pattern
            pattern , range_info = get_recurring_event_office_pattern(self)

        # - create event data
        end = self.start + timedelta(seconds=self.duration)

        c = self.contact

        from home.templatetags.home_extras import formatted_phone_number
        from em.officeservice import update_event
        try:
            ph_number = formatted_phone_number(c.default_phone.phone_number)
        except:
            ph_number = ''
        try:
            cnt_cmp_name = c.contact_company.name
        except:
            cnt_cmp_name = ''
        c_name = ''
        try:
            if self.contact.company.people_tab:
                pers = self.personnels()
                for per in pers:
                    c_name = per.personnel.fullname()
            else:
                c_name = c.fullname()
        except:
            pass

        desc = '''<p><strong>%s</strong></p><p><strong>%s</strong></p><p>%s</p><p>%s</p><p>%s</p><p>Notes: %s</p>
            ''' % (c_name, cnt_cmp_name, c.full_address(), ph_number, c.email, self.notes)
        # - create event in office 365
        userTimezone = self.user.userprofile.get_user_timezone()
        params = {
            'subject': self.google_cal_summary(),
            'body': {
                'contentType': 'HTML',
                'content': desc,
            },
            'start': {
                'dateTime': self.start.strftime('%Y-%m-%dT%H:%M:00'),
                'timeZone': userTimezone
            },
            "end": {
                'dateTime': end.strftime('%Y-%m-%dT%H:%M:00'),
                'timeZone': userTimezone
            },
            "recurrence": {'pattern': pattern,
                           'range': range_info} if pattern is not None and range_info is not None else None
        }
            
        res = update_event(oat.token, uoc.item_id, self.office_item_id, params)

        # - save response
        if res and 'error' in res.keys():
            self.office_html_link = None
            self.office_item_id = None
            self.save()
            return 'redirect'
        else:
            self.office_html_link = res['webLink']
            self.office_item_id = res['id']
            self.save()


    def rm_cal_event(self):
        try:
            ugc = self.user.userprofile.cal_followup
        except:
            ugc = None

        if ugc is None:
            return

        now = timezone.localtime(timezone.now())
        at = AccessToken.objects.filter(user=self.user, expires__gte=now).first()
        if at is None:
            rt = RefreshToken.objects.filter(user=self.user).first()
            if rt:
                at = rt.get_new_access_token()

        if at:
            h = http.client.HTTPSConnection('www.googleapis.com')
            headers = {
                "Content-type": "application/json",
                "Authorization": "Bearer %s" % at.token
            }

            path = '/calendar/v3/calendars/%s/events/%s' % (ugc.item_id, self.item_id)

            h.request('DELETE', path, None, headers)
            r = h.getresponse()

            try:
                result = r.read().strip()
            except:
                result = None

    def rm_office_cal_event(self):
        from appointments.views import get_office_token
        oat = get_office_token(self.user)
        if oat:
            officeservice.delete_event(oat.token, self.office_item_id)

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))

    def followup_length(self):
        return get_duration_time(self.duration)

    def formatted_start(self):
        return '%s' % \
               timezone.localtime(self.start,
                                  timezone.get_current_timezone()).strftime('%Y-%m-%d %H:%M:%S')

    def start_time(self):
        masked_start_time = timezone.localtime(self.start, timezone.get_current_timezone())
        return '%s%s' % \
               (int(masked_start_time.strftime('%I')),
                masked_start_time.strftime(':%M%P').lower())

    def personnels(self):
        return FollowupPersonnel.objects.filter(followup=self)


class StatEventHourly(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    event_type = models.ForeignKey(EventType, on_delete=models.CASCADE)
    date = models.DateField()
    hour = models.IntegerField()
    count = models.IntegerField()
    points = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.event_type.name,
            self.date,
            self.hour,
            self.count)


class StatEventDaily(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    event_type = models.ForeignKey(EventType, on_delete=models.CASCADE)
    date = models.DateField()
    count = models.IntegerField()
    points = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.event_type.name,
            self.date,
            self.count)


class StatCallHourly(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    call_type = models.ForeignKey(CallType, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    date = models.DateField()
    hour = models.IntegerField()
    count = models.IntegerField()
    duration = models.IntegerField()
    personal = models.BooleanField(default=False)

    def __str__(self):
        return '%s %s %s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.call_type.name,
            self.date,
            self.hour,
            self.count,
            self.duration)


class StatCallDaily(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    call_type = models.ForeignKey(CallType, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    date = models.DateField()
    count = models.IntegerField()
    duration = models.IntegerField()
    personal = models.BooleanField(default=False)

    def __str__(self):
        return '%s %s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.call_type.name,
            self.date,
            self.count,
            self.duration)


class StatApptHourly(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    date = models.DateField()
    hour = models.IntegerField()
    count = models.IntegerField()
    duration = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.date,
            self.hour,
            self.count,
            self.duration)


class StatApptDaily(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    date = models.DateField()
    count = models.IntegerField()
    duration = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.date,
            self.count,
            self.duration)


class StatWebinarHourly(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    date = models.DateField()
    hour = models.IntegerField()
    count = models.IntegerField()
    duration = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.date,
            self.hour,
            self.count,
            self.duration)


class StatWebinarDaily(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    date = models.DateField()
    count = models.IntegerField()
    duration = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.date,
            self.count,
            self.duration)


class StatFollowupHourly(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    date = models.DateField()
    hour = models.IntegerField()
    count = models.IntegerField()
    duration = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.date,
            self.hour,
            self.count,
            self.duration)


class StatFollowupDaily(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    date = models.DateField()
    count = models.IntegerField()
    duration = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s' % (
            self.user.userprofile.fullname, self.company.name, self.date, self.count, self.duration)


class StatEmailDaily(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    date = models.DateField()
    count = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.date,
            self.count)


class UserSetting(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    name = models.CharField(max_length=32)
    value = models.CharField(max_length=255)
    manager_daily_activity_additional_email = models.TextField()
    manager_summary_rep_additional_email = models.TextField()
    report_type = models.CharField(max_length=1, null=True, blank=True)
    updated = models.DateTimeField()

    def __str__(self):
        return '%s: %s: %s' % (self.user, self.name, self.value)

    def get_addition_emails(self, string_format=True):
        emails = ReportAdditionalEmail.objects \
            .filter(user_setting=self).values_list('email', flat=True).order_by('id')
        if string_format:
            return ', '.join(emails)
        else:
            return emails


class CompanySetting(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=32)
    value = models.CharField(max_length=64)
    report_start_day = models.CharField(max_length=1, null=True, blank=True)
    updated = models.DateTimeField()


class EmailType(models.Model):
    name = models.CharField(max_length=32)

    def __str__(self):
        return self.pretty_name()

    def pretty_name(self):
        return '%s' % self.name.replace('_', ' ').title() \
            if self.name != 'ai_call_summary_notification' else 'AI Call Summary Notification'


class EmailStatus(models.Model):
    name = models.CharField(max_length=32)

    def __str__(self):
        return self.pretty_name()

    def pretty_name(self):
        return '%s' % self.name.replace('_', ' ').title()


class Email(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='email_user')
    email_type = models.ForeignKey(EmailType, on_delete=models.CASCADE)
    email_status = models.ForeignKey(EmailStatus, on_delete=models.CASCADE)
    hashed = models.CharField(max_length=40)
    subject = models.CharField(max_length=255)
    txt = models.TextField()
    html = models.TextField()
    report = models.ForeignKey('Report', null=True, blank=True, on_delete=models.SET_NULL)
    export_run = models.ForeignKey('ExportRun', null=True, blank=True, on_delete=models.SET_NULL)
    opened = models.DateTimeField(null=True, blank=True)
    attempts = models.IntegerField()
    retry = models.DateTimeField(null=True, blank=True)
    updated = models.DateTimeField()
    created = models.DateTimeField()
    email = models.CharField(max_length=150)

    def pretty_date(self):
        return '%s' % self.created.strftime('%Y-%m-%d')

    def get_attachments(self):
        return EmailFileAttachment.objects.filter(email=self).order_by('id')

    def get_zip_attachments(self):
        return EmailZipFileAttachment.objects.filter(email=self).order_by('id')


class EmailFileAttachment(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    email = models.ForeignKey(Email, on_delete=models.CASCADE)
    name = models.CharField(max_length=80)
    mime_type = models.CharField(max_length=16)
    contents = models.TextField()
    hashed = models.CharField(max_length=40)

    def file_ext(self):
        return self.mime_type.split('/')[1]


class APKVersion(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    cp_version = models.IntegerField()
    android_version = models.IntegerField()
    resolution = models.CharField(max_length=12)
    product = models.CharField(max_length=32)
    created = models.DateTimeField()
    device_name = models.TextField()
    is_tablet = models.BooleanField(default=False)
    application_name = models.CharField(max_length=50, null=True)
    android_api_version = models.CharField(max_length=10)
    android_apk_version = models.CharField(max_length=10)
    is_callLog_build = models.BooleanField(default=False)


class IOSVersion(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    cp_version = models.CharField(max_length=16)
    ios_version = models.CharField(max_length=16)
    resolution = models.CharField(max_length=12)
    product = models.CharField(max_length=32)
    created = models.DateTimeField()
    device_name = models.TextField()
    is_tablet = models.BooleanField(default=False)
    application_name = models.CharField(max_length=50, null=True)


class AutoAction(models.Model):
    name = models.CharField(max_length=64)

    def get_name(self):
        n = self.name.replace('_', ' ')
        return n.title()


class CFieldAuto(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    cfield = models.ForeignKey(CField, on_delete=models.CASCADE)
    action = models.ForeignKey(AutoAction, on_delete=models.CASCADE)
    cfield_1 = models.ForeignKey(CField,
                                 related_name='cfieldauto_cfield_1',
                                 on_delete=models.CASCADE)
    cfield_2 = models.ForeignKey(CField,
                                 related_name='cfieldauto_cfield_2',
                                 on_delete=models.CASCADE)
    hide = models.BooleanField(default=False)


# a single field option
class CFieldOption(models.Model):
    cfield = models.ForeignKey(CField, on_delete=models.CASCADE)
    position = models.IntegerField()
    name = models.CharField(max_length=255, null=True, blank=True)
    points = models.IntegerField(default=0)

    def is_default(self):
        is_default = False
        if self.cfield.cfield_type.name == 'multiple_select':
            try:
                DefaultMultiOption.objects.get(cfield=self.cfield, cfield_option=self)
                is_default = True
            except:
                pass
        else:
            default = self.cfield.cfield_option_default
            is_default = bool(default and default.id == self.id)
        return is_default

    def to_hash(self):
        is_default = '1' if self.is_default() else '0'

        data = {
            'id': self.id,
            'name': self.name,
            'cfield_id': self.cfield_id,
            'cfield': self.cfield.name,
            'is_default': is_default,
            'position': self.position,
            'points': self.points,
        }

        return data


# custom field data
class CFieldValue(models.Model):
    cfield = models.ForeignKey(CField, on_delete=models.CASCADE)
    entity_id = models.IntegerField()
    cf_value = models.TextField()
    updated = models.DateTimeField()

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))


# custom field data
class CFieldMultiValue(models.Model):
    cfield = models.ForeignKey(CField, on_delete=models.CASCADE)
    entity_id = models.IntegerField()
    option = models.ForeignKey(CFieldOption, on_delete=models.CASCADE)
    updated = models.DateTimeField()

    def get_updated(self):
        import time
        return int(time.mktime(self.updated.timetuple()))


class DefaultMultiOption(models.Model):
    cfield = models.ForeignKey(CField, on_delete=models.CASCADE)
    cfield_option = models.ForeignKey(CFieldOption, on_delete=models.CASCADE)


class Trace(models.Model):
    app_version_code = models.TextField(null=True, blank=True)
    app_version_name = models.TextField(null=True, blank=True)
    package_name = models.TextField(null=True, blank=True)
    trace = models.TextField(null=True, blank=True)
    count = models.IntegerField()


class Crash(models.Model):
    trace = models.ForeignKey(Trace, on_delete=models.CASCADE)
    phone_model = models.TextField(null=True, blank=True)
    brand = models.TextField(null=True, blank=True)
    product = models.TextField(null=True, blank=True)
    android_version = models.TextField(null=True, blank=True)
    build = models.TextField(null=True, blank=True)
    total_mem_size = models.TextField(null=True, blank=True)
    available_mem_size = models.TextField(null=True, blank=True)
    initial_configuration = models.TextField(null=True, blank=True)
    crash_configuration = models.TextField(null=True, blank=True)
    display = models.TextField(null=True, blank=True)
    user_comment = models.TextField(null=True, blank=True)
    dumpsys_meminfo = models.TextField(null=True, blank=True)
    device_features = models.TextField(null=True, blank=True)
    environment = models.TextField(null=True, blank=True)
    shared_preferences = models.TextField(null=True, blank=True)
    settings_system = models.TextField(null=True, blank=True)
    settings_secure = models.TextField(null=True, blank=True)
    created = models.DateTimeField()


class ContactRep(models.Model):
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    created = models.DateTimeField()


class CallOverride(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    phone_number = models.CharField(max_length=11)
    contact_phone = models.ForeignKey(ContactPhone, on_delete=models.CASCADE)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class OppType(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    position = models.IntegerField()

    def can_move_up(self):
        ot = OppType.objects.filter(company=self.company, position__lt=self.position).first()
        return True if ot else False

    def can_move_down(self):
        ot = OppType.objects.filter(company=self.company, position__gt=self.position).first()
        return True if ot else False


class OppStage(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    fg_color = models.CharField(max_length=7)
    bg_color = models.CharField(max_length=7)
    fg_color2 = models.CharField(max_length=7)
    bg_color2 = models.CharField(max_length=7)
    position = models.IntegerField()
    probability = models.IntegerField(default=0)
    lock = models.BooleanField(default=False)

    def can_move_up(self):
        ot = OppStage.objects.filter(company=self.company, position__lt=self.position).first()
        return True if ot else False

    def can_move_down(self):
        ot = OppStage.objects.filter(company=self.company, position__gt=self.position).first()
        return True if ot else False

    def notifications(self):
        emails = ''
        for ose in OppStageEmail.objects.filter(opp_stage=self).order_by('id'):
            emails += '%s\n' % ose.email
        return emails


class OppStageEmail(models.Model):
    opp_stage = models.ForeignKey(OppStage, on_delete=models.CASCADE)
    email = models.CharField(max_length=150)


class Opp(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    opp_stage = models.ForeignKey(OppStage, on_delete=models.CASCADE)
    opp_type = models.ForeignKey(OppType, null=True, blank=True, on_delete=models.SET_NULL)
    probability = models.IntegerField()
    value = models.DecimalField(max_digits=11, decimal_places=2)
    close_date = models.DateTimeField()
    notes = models.TextField()
    opp_name = MyCharField(max_length=100, null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def derived(self):
        oh = OppHistory.objects.filter(opp=self).order_by('-id').first()
        if oh:
            return oh.value * oh.probability / 100
        return 0

    def to_hash(self):
        other_contacts = [{'id': oc.contact_id, 'name': oc.contact.fullname()} for oc in
                          OppContact.objects.filter(opp=self)]
        try:
            derived = str(self.value * self.probability / 100)
        except:
            derived = ''
        try:
            close_date = self.created.strftime('%Y-%m-%d %H:%M:%S')
            updated = self.updated.strftime('%Y-%m-%d %H:%M:%S')
        except:
            close_date = ''
            updated = ''
        try:
            rep = self.user.userprofile.to_hash()
        except:
            rep = {}
        data = {
            'opp_id': self.id,
            'rep': rep,
            'contact_name': self.contact.fullname(),
            'contact_id': self.contact_id,
            'opp_type_id': self.opp_type_id,
            'opp_stage_id': self.opp_stage_id,
            'opp_name': self.opp_name,
            'value': str(self.value),
            'probability': str(self.probability),
            'derived': derived,
            'created': self.created.strftime('%Y-%m-%d %H:%M:%S'),
            'updated': updated,
            'close_date': close_date,
            'other_contacts': other_contacts,
            'notes': self.notes
        }

        return data

    def get_personnels(self):
        data_list = list(self.opppersonnel_set.all().select_related('personnel'))
        return data_list

    def get_history(self):
        opp_histories = OppHistory.objects.filter(opp=self).order_by('-id')
        return opp_histories

    def get_more_contacts(self):
        data_list = list(self.oppcontact_set.all().select_related('contact'))
        return data_list


class OppContact(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    opp = models.ForeignKey(Opp, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    created = models.DateTimeField()


class OppPersonnel(models.Model):
    opp = models.ForeignKey(Opp, on_delete=models.CASCADE)
    personnel = models.ForeignKey(ContactPersonnel, on_delete=models.CASCADE)


class OppHistory(models.Model):
    opp = models.ForeignKey(Opp, on_delete=models.CASCADE)
    opp_stage = models.ForeignKey(OppStage, on_delete=models.CASCADE)
    opp_type = models.ForeignKey(OppType, null=True, blank=True, on_delete=models.SET_NULL)
    probability = models.IntegerField()
    value = models.DecimalField(max_digits=11, decimal_places=2)
    close_date = models.DateTimeField()
    created = models.DateTimeField()
    notes = models.TextField()
    opp_name = MyCharField(max_length=100, null=True, blank=True)


class AccessToken(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    token = models.TextField()
    id_token = models.CharField(max_length=1024)
    expires = models.DateTimeField()


class RefreshToken(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    token = models.TextField()
    device = models.CharField(max_length=7, default='web')

    def get_encrypted_id(self):
        """
        Encrypt the id of the RefreshToken so that it can be stored in the client cookie
        in a way that makes it impossible to be used directly.
        @return: encrypted string, containing the id of the RefreshToken
        """
        plain_text = RefreshToken.pad(str(self.id))
        iv = Crypto.Random.get_random_bytes(AES.block_size)
        cipher = AES.new(settings.COOKIE_SALT.encode("utf8"), AES.MODE_CFB, iv)
        return base64.b64encode(iv + cipher.encrypt(plain_text.encode())).decode()

    @staticmethod
    def get_decrypted_id(secret):
        """
        Decode a string from the encrypted id back to an integer
        @param secret:
        @return:
        """
        ciphertext = base64.b64decode(secret)
        iv = ciphertext[:AES.block_size]
        cipher = AES.new(settings.COOKIE_SALT.encode("utf8"), AES.MODE_CFB, iv)
        decrypted_byte_array = cipher.decrypt(ciphertext[AES.block_size:])
        decrypted_string = decrypted_byte_array.decode().rstrip('{')
        return int(decrypted_string)

    @staticmethod
    def pad(target_string):
        """
        Strings encrypted using AES.MODE_CFB must be a multiple of 32 characters
        in length. This function will automatically pad a string to an appropriate multiple
        of 32 characters, using the hard-coded character below.
        @param target_string: The string to pad
        @return: the padded string
        """
        return target_string + (32 - len(target_string) % 32) * '{'

    def get_new_access_token(self):
        if self.device == 'ios':
            client_id = settings.GA_CLIENT_ID_IDEAVATE_IOS
            client_secret = settings.GA_CLIENT_SECRET_IDEAVATE_IOS
        elif self.device == 'android':
            client_id = settings.GA_CLIENT_ID_IDEAVATE
            client_secret = settings.GA_CLIENT_SECRET_IDEAVATE
        else:
            client_id = settings.GA_CLIENT_ID
            client_secret = settings.GA_CLIENT_SECRET

        data = urllib.parse.urlencode({'client_id': client_id,
                                       'client_secret': client_secret,
                                       'refresh_token': self.token,
                                       'grant_type': 'refresh_token'})

        h = http.client.HTTPSConnection('accounts.google.com')
        headers = {"Content-type": "application/x-www-form-urlencoded", "Accept": "text/plain"}
        h.request('POST', '/o/oauth2/token', data, headers)
        r = h.getresponse()
        j = r.read()
        a = json.loads(j)

        try:
            access_token = a['access_token']
        except:
            access_token = None

        try:
            id_token = a['id_token']
        except:
            id_token = None

        try:
            expires_in = int(a['expires_in'])
        except:
            expires_in = None

        at = None

        if access_token and expires_in and id_token:
            for at in AccessToken.objects.filter(user=self.user):
                at.delete()
            expires = timezone.localtime(timezone.now()) + timedelta(seconds=expires_in)
            at = AccessToken(user=self.user, token=access_token, id_token=id_token, expires=expires)
            at.save()

        return at


class OfficeAccessToken(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    token = models.TextField()
    id_token = models.TextField()
    expires = models.DateTimeField()


class OfficeRefreshToken(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    token = models.TextField()
    device = models.CharField(max_length=7, default='web')

    def get_new_access_token(self):
        for_web = self.device not in ['ios', 'android']
        response = officeservice \
            .get_token_from_refresh_token(self.token,
                                          settings.CALENDAR_REDIRECT_URI,
                                          officeservice.cal_scopes,
                                          for_web)
        try:
            access_token = response['access_token']
        except:
            access_token = None

        try:
            expires_in = response['expires_in']
        except:
            expires_in = None

        try:
            refresh_token = response['refresh_token']
        except:
            refresh_token = None

        oat = None
        if access_token and expires_in:
            try:
                oat = OfficeAccessToken.objects.filter(user=self.user)[:1][0]
            except:
                oat = OfficeAccessToken(user=self.user)
            oat.token = access_token
            oat.expires = timezone.localtime(timezone.now()) + timedelta(seconds=expires_in)

            oat.save()
            self.token = refresh_token
            self.save()

        return oat


class GoogleContact(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, null=True, blank=True, on_delete=models.SET_NULL)
    first_name = MyCharField(max_length=32, null=True, blank=True)
    last_name = models.CharField(max_length=32, null=True, blank=True)
    email = models.CharField(max_length=64, null=True, blank=True)
    address = models.CharField(max_length=80, null=True, blank=True)
    address2 = models.CharField(max_length=80, null=True, blank=True)
    city = models.CharField(max_length=64, null=True, blank=True)
    state = models.ForeignKey(State, on_delete=models.SET_NULL, null=True, blank=True)
    zip = models.CharField(max_length=10, null=True, blank=True)
    country = models.ForeignKey(Country, on_delete=models.SET_NULL, null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s %s' % (self.first_name, self.last_name)

    def full_address(self):
        state = self.state.abbr if self.state else ''
        if state == 'null':
            state = ''
        address = self.address if self.address else ''
        if address == 'null':
            address = ''
        city = self.city if self.city else ''
        if city == 'null':
            city = ''
        zip = self.zip if self.zip else ''
        if zip == 'null':
            zip = ''
        addr = '%s %s %s %s' % (address, city, state, zip)
        addr = addr.replace('  ', ' ').strip()
        return addr

    def get_contact_phones(self):
        return self.googlecontactphone_set.all()


class GoogleContactPhone(models.Model):
    google_contact = models.ForeignKey('GoogleContact', on_delete=models.CASCADE)
    phone_type = models.ForeignKey(PhoneType, on_delete=models.CASCADE)
    phone_number = models.CharField(max_length=10)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s - %s - %s' % \
               (self.google_contact.__str__(), self.phone_number, self.phone_type.__str__())


class GooglePlaceType(models.Model):
    name = models.CharField(max_length=64, unique=True)

    def __str__(self):
        return '%s' % self.name


class GooglePlaceSearch(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    created_by = models.ForeignKey(User, on_delete=models.CASCADE)
    name = models.CharField(max_length=64, null=True, blank=True)
    latitude = models.CharField(max_length=12)
    longitude = models.CharField(max_length=12)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    class Meta:
        indexes = [models.Index(fields=['company', 'latitude', 'longitude'],
                                name='company_latitude_longitude')]

    def __str__(self):
        return '%s %s' % (self.latitude, self.longitude)

    def get_google_places(self):
        return GooglePlace.objects.filter(gp_search=self).order_by('id')


class GooglePlaceSearchType(models.Model):
    gp_search = models.ForeignKey(GooglePlaceSearch, on_delete=models.CASCADE)
    gp_type = models.ForeignKey(GooglePlaceType, on_delete=models.CASCADE)


class GooglePlace(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    created_by = models.ForeignKey(User, on_delete=models.CASCADE)
    gp_search = models.ForeignKey(GooglePlaceSearch,
                                  null=True,
                                  blank=True,
                                  on_delete=models.SET_NULL)
    gp_id = models.TextField() # CPV1-2520 Apple Map issue change the filed type
    reference = models.CharField(max_length=512)
    name = MyCharField(max_length=255, null=True, blank=True)
    vicinity = models.CharField(max_length=255)
    address = models.CharField(max_length=255, null=True, blank=True)
    city = models.CharField(max_length=80, null=True, blank=True)
    state = models.ForeignKey(State, on_delete=models.SET_NULL, null=True, blank=True)
    zip = models.CharField(max_length=10, null=True, blank=True)
    country = models.ForeignKey(Country, on_delete=models.SET_NULL, null=True, blank=True)
    phone_number = models.CharField(max_length=10, null=True, blank=True)
    website = models.CharField(max_length=255, null=True, blank=True)
    latitude = models.DecimalField(max_digits=11, decimal_places=7)
    longitude = models.DecimalField(max_digits=11, decimal_places=7)
    distance = models.DecimalField(max_digits=11, decimal_places=2)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    business_type = models.TextField(blank=True, null=True)
    employee_count = models.CharField(max_length=50, blank=True, null=True)
    annual_sales = models.CharField(max_length=125, blank=True, null=True)
    county = models.CharField(max_length=255, blank=True, null=True)
    contact_name = models.CharField(max_length=255, blank=True, null=True)
    title = models.CharField(max_length=50, blank=True, null=True)

    class Meta:
        indexes = [models.Index(fields=['company', 'gp_id', 'name', 'address', 'created_by'],
                                name='cmpny_gp_name_addrs_created_by')]

    def __str__(self):
        return '%s' % self.name

    def get_distance(self):
        return '%.1fM' % self.distance

    def get_m_title(self):
        return '%s|%s' % (self.id, self.name.strip().replace(':', '').replace('/', ''))

    def place_name(self):
        return '%s' % (self.__str__())

    def full_address(self):
        state = self.state.abbr if self.state else ''
        addr = '%s %s %s %s' % (self.address, self.city, state, self.zip)
        return addr.replace('  ', ' ').strip()

    def get_details(self):
        pnp = re.compile('[^0-9]')

        pattern = 'https://maps.googleapis.com/maps/api/place/details/json?fields=%s&reference=%s&sensor=false&v=3&key=%s'
        url = pattern % (constants.MAP_SEARCH_FIELDS, self.reference, settings.GA_SIMPLE_API)

        req = urllib.request.Request(url)
        opener = urllib.request.build_opener(urllib.request.HTTPSHandler(debuglevel=0))

        reply = None
        a = None

        try:
            req = opener.open(req)
        except:
            req = None

        if req:
            try:
                reply = req.read()
            except:
                reply = None

            req.close()

        if reply:
            try:
                a = json.loads(reply)
            except:
                a = None

        try:
            status = a['status']
        except:
            status = None

        if status and status == 'OK':
            try:
                from home.templatetags.home_extras import formatted_phone_number
                phone_number = pnp.sub('', a['result']['formatted_phone_number'])
            except:
                phone_number = ''

            if len(phone_number) == 11 and phone_number[0] == '1':
                phone_number = phone_number[1:11]
            elif len(phone_number) > 10:
                phone_number = phone_number[:10]

            try:
                website = a['result']['website'][:255]
            except:
                website = ''

            address = None
            city = None
            state = None
            country = None
            zip = None

            try:
                address_components = a['result']['address_components']
            except:
                address_components = None

            if address_components and len(address_components) > 0:
                for ac in address_components:
                    if 'street_number' in ac['types']:
                        address = ac['long_name']

                    if 'route' in ac['types']:
                        if address:
                            address = address + ' ' + ac['long_name']
                        else:
                            address = ac['long_name']

                    if 'locality' in ac['types']:
                        city = ac['long_name']

                    if 'administrative_area_level_1' in ac['types']:
                        state_name = ac['long_name']

                    if 'country' in ac['types']:
                        country_name = ac['long_name']
                        if country_name == 'US':
                            country_name = 'United States'
                        country = Country.objects.filter(name=country_name).first()

                        if state_name and country_name:
                            state = State.objects.filter(abbr=state_name,
                                                         province=country_name).first()
                            if not state:
                                state = State.objects.filter(name=state_name,
                                                             province=country_name).first()

                    if 'postal_code' in ac['types']:
                        zip = ac['long_name']
                        if len(zip) > 10:
                            zip = zip[:10]

                        if len(zip) == 4:
                            zip = '0%s' % zip

            if address:
                self.address = address
            if city:
                self.city = city
            if state:
                self.state = state
            if zip:
                self.zip = zip
            if country:
                self.country = country
            if phone_number:
                self.phone_number = phone_number

            if website:
                self.website = website

            self.updated = timezone.localtime(timezone.now())
            self.save()

    def get_here_map_places_details(self):
        pnp = re.compile('[^0-9]')
        results = get_here_map_response(self.reference)

        if results:
            try:
                result_address = results['location']['address']
                result_contact = results['contacts']
            except:
                return False

            try:
                phone_number = pnp.sub('', result_contact['phone'][0]['value'])
            except:
                phone_number = ''

            if len(phone_number) == 11 and phone_number[0] == '1':
                phone_number = phone_number[1:11]
            elif len(phone_number) > 10:
                phone_number = phone_number[:10]

            try:
                website = result_contact['website'][0]['value'][:255]
            except:
                website = ''

            try:
                house_no = result_address['house']
            except:
                house_no = ''

            try:
                street = result_address['street']
            except:
                street = ''
            address = house_no + street
            try:
                state = State.objects.filter(name=result_address['state'])[:1][0]
            except:
                state = None
            try:
                country = Country.objects.filter(name=result_address['country'])[:1][0]
            except:
                country = Country.objects.filter(name='United States')[:1][0]
            try:
                zip = result_address['postalCode']
            except:
                zip = ''
            try:
                city = result_address['city']
            except:
                city = ''

            if address:
                self.address = address
            if city:
                self.city = city
            if state:
                self.state = state
            if zip:
                self.zip = zip
            if country:
                self.country = country
            if phone_number:
                self.phone_number = phone_number

            if website:
                self.website = website

            self.updated = timezone.localtime(timezone.now())
            self.save()
            return True
        return False

    def record_color(self, user):
        color = ''

        # Create a subquery for the phone numbers
        contacts_with_phone_number = \
            ContactPhone.objects.filter(contact__company=self.company,
                                        phone_number=self.phone_number.strip()).values("contact")

        # Get the user_id's of ContactReps who:
        #   - Are in the same Company -and-
        #       - The Contact is referenced by this place -or-
        #       - The Company Name of the referenced Contact is a case-insensitive match -or-
        #       - The Contact is in the list of Contacts that share a phone number with this Place
        contact_reps = ContactRep.objects \
            .filter(contact__company=self.company) \
            .filter(Q(contact__place=self) |
                    Q(contact__contact_company__name__iexact=self.name) |
                    Q(contact__in=contacts_with_phone_number)) \
            .distinct()

        # Using the list of user_id's associated with this GooglePlace,
        # identify the icon color to be used, based on whether the rep assignments
        # in relation to the current user.
        user_ids = contact_reps.values_list("user_id", flat=True)
        if len(user_ids) == 0:
            # default to no associations
            color = ''
        elif len(user_ids) == 1:
            if user.id in user_ids:
                # This user is the only rep assigned to the Contact
                color = 'green'
            else:
                # Someone else is assigned to the Contact
                color = 'red'
        elif user.id in user_ids:
            # This user is one of multiple reps assigned to the Contact
            color = 'yellow'

        # If this GooglePlace is associated with a Contact based on the search criteria, 
        #   make sure to update the database accordingly to indicate a match was found.
        if color != '':
            # Iterate over the ContactReps and for each whose Contact isn't assigned to
            # this GooglePlace, assign it.
            for contact_rep in contact_reps:
                if contact_rep.contact.place_id is None:
                    contact_rep.contact.place = self
                    contact_rep.contact.save()
        return color


class BillingOpt(models.Model):
    name = models.CharField(max_length=64)
    description = models.CharField(max_length=255)
    active = models.BooleanField(default=True)

    def name_short(self):
        if self.name.find('Credit Card') >= 0:
            return 'Credit Card'
        return self.name


class Plan(models.Model):
    name = models.CharField(max_length=64)
    description = models.CharField(max_length=255)
    price = models.DecimalField(max_digits=7, decimal_places=2)
    active = models.BooleanField(default=True)


class Membership(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    plan = models.ForeignKey(Plan, on_delete=models.CASCADE)
    billing_opt = models.ForeignKey(BillingOpt, null=True, blank=True, on_delete=models.SET_NULL)
    billing_date = models.DateField(null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class Billing(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    plan = models.ForeignKey(Plan, on_delete=models.CASCADE)
    start_date = models.DateTimeField()
    end_date = models.DateTimeField(null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class Invoice(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    invoice_date = models.DateTimeField()
    desc = models.TextField(max_length=4096)
    amount = models.DecimalField(max_digits=7, decimal_places=2)
    active = models.BooleanField(default=False)
    paid = models.BooleanField(default=False)
    paid_date = models.DateTimeField(null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s' % self.id

    def still_owe(self):
        return self.amount - self.payments()

    def payments(self):
        total = 0
        for p in Payment.objects.filter(company=self.company, invoice=self):
            total += p.amount
        return total

    def html_desc(self):
        return self.desc.replace('\r\n\r\n', '\r\n').replace('\n\n', '\n').replace('\n', '<br />')

    def html_desc_short(self):
        desc = self.desc.replace('\r\n\r\n', '\r\n').replace('\n\n', '\n').strip()
        if len(desc) > 72:
            desc = '%s...' % desc[:72]
        return desc.replace('\n', '<br />')

    def invoice_date_short(self):
        return self.invoice_date.strftime('%B %d, %Y')


class Payment(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    invoice = models.ForeignKey(Invoice, null=True, blank=True, on_delete=models.SET_NULL)
    billing_opt = models.ForeignKey(BillingOpt, on_delete=models.CASCADE)
    amount = models.DecimalField(max_digits=7, decimal_places=2)
    auth_code = models.CharField(max_length=80, null=True, blank=True)
    trans_id = models.CharField(max_length=80, null=True, blank=True)
    check_number = models.CharField(max_length=80, null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s' % self.id

    def payment_date_short(self):
        return self.created.strftime('%B %d, %Y')


class ScriptServer(models.Model):
    name = models.CharField(max_length=64, null=True, blank=True)

    def __str__(self):
        return '%s' % self.name

    @staticmethod
    def add():
        import socket
        n = socket.gethostname()
        n = n.lower()[:64]
        ss = ScriptServer.objects.filter(name__iexact=n).first()
        if ss:
            return ss
        ss = ScriptServer(name=n)
        ss.save()
        return ss


class ScriptType(models.Model):
    name = models.CharField(max_length=64, null=True, blank=True)

    def __str__(self):
        return '%s' % self.name


class ScriptRun(models.Model):
    script_server = models.ForeignKey(ScriptServer, on_delete=models.CASCADE)
    script_type = models.ForeignKey(ScriptType, on_delete=models.CASCADE)
    output = models.TextField(max_length=4096)
    duration = models.DecimalField(max_digits=19, decimal_places=10, null=True,
                                   blank=True, default=0)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s - %s - %s' % (self.script_type.name, self.created, self.duration)


class TwilioCallType(models.Model):
    name = models.CharField(max_length=32)

    def __str__(self):
        return '%s' % self.name

    def pretty_name(self):
        return '%s' % self.name.replace('_', ' ').title()


class TwilioCallResult(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    result = models.CharField(max_length=255)
    contact_type_name = models.CharField(max_length=100)
    deleted = models.BooleanField(default=False)

    def __str__(self):
        return '%s' % self.result


class TwilioCallerID(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE, null=True, blank=True)
    user_phone = models.ForeignKey(UserPhone, null=True, blank=True, on_delete=models.SET_NULL)
    dealer_store_phone = models.ForeignKey('DealerStorePhone', null=True,
                                           blank=True, on_delete=models.SET_NULL)
    code = models.CharField(max_length=16)
    name = models.CharField(max_length=64)
    call_sid = models.CharField(max_length=48, null=True, blank=True)
    sid = models.CharField(max_length=48, null=True, blank=True)
    validated = models.BooleanField(default=False)
    status = models.CharField(max_length=32)

    def __str__(self):
        return '%s %s %s %s' % (self.company, self.user, self.user_phone, self.dealer_store_phone)

    def get_phone_number(self):
        from home.templatetags.home_extras import formatted_phone_number
        if self.dealer_store_phone:
            us = UserSetting.objects.filter(user=self.user, name='store_phone_caller_id').first()

            if us:
                sp = DealerStorePhone.objects.filter(id=us.value).first()
                if sp and sp.dealer_store.company == self.company:
                    cid = TwilioCallerID.objects.filter(dealer_store_phone=sp,
                                                        validated=True).first()

                    if cid:
                        try:
                            ext = sp.country_code
                            if ext is None or ext == '':
                                ext = '+1'
                        except:
                            ext = '+1'
                        return ext + ' %s' % formatted_phone_number(sp.phone_number)
            try:
                ext1 = self.dealer_store_phone.country_code
                if ext1 is None or ext1 == '':
                    ext1 = '+1'
            except:
                ext1 = '+1'
            return ext1 + ' %s' % formatted_phone_number(self.dealer_store_phone.phone_number)

        elif self.user:
            try:
                up = self.user.userprofile
            except:
                up = None

            if up and up.default_phone:
                cid = TwilioCallerID.objects.filter(user=self.user,
                                                    user_phone=up.default_phone,
                                                    validated=True).first()
                if cid:
                    try:
                        exte = up.default_phone.country_code
                        if exte is None or exte == '':
                            exte = '+1'
                    except:
                        exte = '+1'
                    return exte + ' %s' % formatted_phone_number(up.default_phone.phone_number)

            cid = TwilioCallerID.objects.filter(user=self.user, validated=True).first()
            if cid:
                try:
                    ext2 = self.user_phone.country_code
                    if ext2 is None or ext2 == '':
                        ext2 = '+1'
                except:
                    ext2 = '+1'
                return ext2 + ' %s' % formatted_phone_number(self.user_phone.phone_number)

        return settings.TWILIO_DEFAULT_EXTENTION + ' %s' % settings.TWILIO_DEFAULT_CALLERID


class TwilioMsg(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    name = models.CharField(max_length=64, null=True, blank=True)
    call_sid = models.CharField(max_length=48)
    url = models.CharField(max_length=255, null=True, blank=True)
    call_status = models.CharField(max_length=16, null=True, blank=True)
    duration = models.IntegerField(null=True, blank=True, default=0)
    deleted = models.BooleanField(default=False)
    created = models.DateTimeField()

    def status(self):
        from home.templatetags.home_extras import formatted_phone_number
        status = 'Unknown'

        up = self.user.userprofile
        phone_number = formatted_phone_number(up.default_phone.phone_number)

        if self.duration in [0, 1]:
            return 'Calling <b>%s</b>' % phone_number
        return 'Call has ended: <b>%s</b>' % self.call_status.title()


class TwilioSMSType(models.Model):
    name = models.CharField(max_length=32)

    def __str__(self):
        return '%s' % self.name


class TwilioSMS(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    contact_phone = models.ForeignKey(ContactPhone, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    twilio_phone = models.ForeignKey('TwilioPhoneNumber', on_delete=models.CASCADE)
    sms_type = models.ForeignKey(TwilioSMSType, on_delete=models.CASCADE)
    start = models.DateTimeField()
    msg = models.TextField()  # CPV1-2719 Change the inbound SMS limitation.
    sent = models.NullBooleanField()
    seen = models.BooleanField(default=False)
    failed = models.BooleanField(default=False)
    carrier_name = models.CharField(max_length=100, null=True, blank=True)
    caller_name = models.CharField(max_length=100, null=True, blank=True)
    is_new_contact_sms = models.BooleanField(default=False)
    wait_time = models.IntegerField(default=0)
    error_detail = models.TextField(null=True, blank=True)

    def status(self):
        if self.sms_type.name == 'incoming':
            return 'Received'
        if self.sms_type.name == 'outgoing' and self.sent:
            return 'Sent'
        if self.failed:
            return 'Failed'
        return 'Queued'

    def get_mms_url(self):
        mms_urls = []
        tmmurls = TwilioMMSurls.objects.filter(twiliosms=self)
        if tmmurls:
            for tm in tmmurls:
                mms_urls.append(tm.mms_url)
        return mms_urls
    
    def save(self, **kwargs):
        """
        Function used to update the opt-in opt-out phone numbers
        """

        incoming_type_id = TwilioSMSType.objects.filter(id=constants.INCOMING_SMS_TYPE)
        if self.msg and self.msg.strip() in ['STOP', 'UNSUBSCRIBE', 'END', 'QUIT', 'HALT'] and \
                self.sms_type_id == incoming_type_id.id:
            contact_phone = ContactPhone.objects.filter(id=self.contact).first()
            try:
                opt_in_number = PhoneNumberMessageConsent.objects.filter(phone_number=contact_phone.phone_number,
                                                                         is_opt_in=True).first()
                opt_in_number.is_opt_in = False
                opt_in_number.save()
            except Exception:
                pass

        super().save(**kwargs)


class CallEvaluation(models.Model):
    name = models.CharField(max_length=50)


class TwilioCall(models.Model):
    call_type = models.ForeignKey(TwilioCallType, on_delete=models.CASCADE)
    tollfree = models.NullBooleanField(null=True, blank=True)
    call_sid = models.CharField(max_length=48)
    first_leg_call_sid = models.CharField(max_length=48, null=True, blank=True)
    twilio_msg = models.ForeignKey(TwilioMsg, null=True, blank=True, on_delete=models.SET_NULL)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, null=True, blank=True, on_delete=models.SET_NULL)
    contact_phone = models.ForeignKey(ContactPhone, null=True, blank=True, on_delete=models.SET_NULL)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    user_phone = models.ForeignKey(UserPhone, null=True, blank=True, on_delete=models.SET_NULL)
    dealer_store_phone = models.ForeignKey('DealerStorePhone',
                                           null=True,
                                           blank=True,
                                           on_delete=models.SET_NULL)
    start = models.DateTimeField()
    duration = models.IntegerField(null=True, blank=True, default=0)
    recording = models.CharField(max_length=255)
    call_status = models.CharField(max_length=16, null=True, blank=True)
    rating = models.IntegerField(null=True, blank=True, default=0)
    call_result = models.ForeignKey(TwilioCallResult,
                                    null=True,
                                    blank=True,
                                    on_delete=models.SET_NULL)
    notes = models.CharField(max_length=4096, null=True, blank=True)
    old_id = models.IntegerField(null=True, blank=True)
    google_place = models.ForeignKey('GooglePlace',
                                     null=True,
                                     blank=True,
                                     on_delete=models.SET_NULL)
    last_lookup = models.DateTimeField(null=True, blank=True)
    lookup_count = models.IntegerField(null=True, blank=True, default=0)
    caller = models.CharField(max_length=20)
    carrier_name = models.CharField(max_length=100, null=True, blank=True)
    caller_name = models.CharField(max_length=100, null=True, blank=True)
    dailer_number = models.CharField(max_length=15, null=True, blank=True)
    twilio_phone = models.ForeignKey('TwilioPhoneNumber',
                                     null=True,
                                     blank=True,
                                     on_delete=models.SET_NULL)
    conference = models.CharField(max_length=16, null=True, blank=True)
    last_beep = models.DateTimeField(null=True, blank=True)
    country_code = models.CharField(max_length=4)
    is_voice_mail = models.BooleanField(default=False, blank=True)
    received_on = models.CharField(max_length=8)
    other_number = models.CharField(max_length=12, null=True, blank=True)
    sip_user = models.CharField(max_length=200, null=True, blank=True)
    call_evaluation = models.ForeignKey(CallEvaluation, null=True, on_delete=models.SET_NULL)
    is_recording_deleted_from_twilio = models.BooleanField(default=False, blank=True)
    is_ai_summary_sent = models.BooleanField(default=False, null=False)

    def beep_bot(self):
        company = self.company
        if not company.twilio_conference or company.beep_minutes <= 0:
            return

        if self.last_beep is None:
            next_beep = timezone.localtime(timezone.now())
        else:
            next_beep = self.last_beep + timedelta(minutes=company.beep_minutes)

        if next_beep <= timezone.localtime(timezone.now()):
            url = '%s/caller/bot/join/%s/' % (settings.APP_URL, self.conference)

            data = urllib.parse.urlencode({'To': settings.TWILIO_BOT_NUMBER,
                                           'From': settings.TWILIO_DEFAULT_CALLERID,
                                           'Url': url,
                                           'StatusCallback': url
                                           })

            h = http.client.HTTPSConnection('api.twilio.com')

            p = base64.b64encode('%s:%s' %
                                 (settings.TWILIO_ACCOUNT_SID, settings.TWILIO_AUTH_TOKEN))

            headers = {'Content-type': 'application/x-www-form-urlencoded',
                       'Accept': 'text/plain',
                       'Authorization': 'Basic %s' % p}

            path = '/2010-04-01/Accounts/%s/Calls' % settings.TWILIO_ACCOUNT_SID

            h.request('POST', path, data, headers)

            r = h.getresponse()

            self.last_beep = next_beep
            self.save()

    def is_followup(self):
        fc = FollowupCall.objects.filter(twilio_call=self).first()
        return True if fc else False

    def ident(self):
        out = '%s %s' % (self, self.lookup_count)
        pn = self.caller

        if not ident_twilio_incoming(self, pn):
            if len(pn) == 11:
                ident_twilio_incoming(self, pn[1:11])
            elif len(pn) == 10:
                ident_twilio_incoming(self, pn[3:10])
        new_lookup_count = self.lookup_count + 1

        if self.last_lookup is None:
            self.last_lookup = timezone.localtime(timezone.now())

        self.last_lookup = self.last_lookup + timedelta(hours=(new_lookup_count * 12))
        self.lookup_count = new_lookup_count
        self.save()

    def file_key(self):
        k = None
        if self.recording.find('/') > -1:
            a = self.recording.split('/')
            k = a[len(a) - 1] if len(a) else None
        return k

    def status(self):
        from home.templatetags.home_extras import formatted_phone_number

        uc = TwilioCallType.objects.filter(name='user_contact')[:1][0]
        bc = TwilioCallType.objects.filter(name='browser')[:1][0]
        ic = TwilioCallType.objects.filter(name='incoming')[:1][0]

        status = 'Unknown'

        if self.call_type == uc:
            if self.duration == 0:
                up = self.user.userprofile
                phone_number = formatted_phone_number(up.default_phone.phone_number)
                status = 'Calling <b>%s</b> at <b>%s</b>' % (up, phone_number)
            elif self.duration == 1:
                if self.call_status == 'leaving-message':
                    status = 'Leaving message'
                else:
                    phone_number = formatted_phone_number(self.contact_phone.phone_number)
                    status = 'Calling <b>%s</b> at <b>%s</b>' % (self.contact, phone_number)
            else:
                status = 'Call has ended: <b>%s</b>' % self.call_status.title()

        elif self.call_type == bc:
            if self.duration == 0:
                status = 'Calling <b>%s</b> at <b>%s</b>' % \
                         (self.user.userprofile,
                          formatted_phone_number(self.user_phone.phone_number))
            elif self.duration == 1:
                if self.call_status == 'leaving-message':
                    status = 'Leaving message'
                else:
                    status = 'Calling <b>%s</b> at <b>%s</b>' % \
                             (self.contact,
                              formatted_phone_number(self.contact_phone.phone_number))
            else:
                status = 'Call has ended: <b>%s</b>' % self.call_status.title()

        elif self.call_type == ic:
            pass

        return status

    def recording_url(self):
        return self.recording

    def get_transcription_text(self):
        text = ''
        if self.tw_id:
            cts = CallTranscriptionTexts.objects.filter(transcription_id=self.tw_id)
            for i in cts:
                text += '[{}]: '.format(i.speaker or 'Speaker')
                text += i.text
                if len(text) > 500:
                    text = text[:500] + '...'
                    break
                text += '<br>'

        return text


class StatTwilioCallHourly(models.Model):
    call_type = models.ForeignKey(TwilioCallType, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    dealer_store = models.ForeignKey('DealerStore', on_delete=models.SET_NULL, null=True, blank=True)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    date = models.DateField()
    hour = models.IntegerField()
    count = models.IntegerField()
    duration = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.date,
            self.hour,
            self.count,
            self.duration)


class StatTwilioCallDaily(models.Model):
    call_type = models.ForeignKey(TwilioCallType, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, blank=True, on_delete=models.SET_NULL)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    dealer_store = models.ForeignKey('DealerStore', on_delete=models.SET_NULL,
                                     null=True, blank=True)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    date = models.DateField()
    count = models.IntegerField()
    duration = models.IntegerField()

    def __str__(self):
        return '%s %s %s %s %s' % (
            self.user.userprofile.fullname,
            self.company.name,
            self.date,
            self.count,
            self.duration)


class StatScriptRunDaily(models.Model):
    script_type = models.ForeignKey(ScriptType, on_delete=models.CASCADE)
    date = models.DateField()
    duration = models.IntegerField()

    def __str__(self):
        return '%s %s' % (self.script_type.name, self.date)


class WufooForm(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, on_delete=models.CASCADE)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    name = models.CharField(max_length=64)
    wufoo_key = models.CharField(max_length=16)
    hash_key = models.CharField(max_length=16)

    def new_contact_url(self):
        return '%s/wufoo/%s/contact/new/' % (settings.APP_URL, self.hash_key)


class RefererURL(models.Model):
    name = models.CharField(max_length=64)
    url = models.CharField(max_length=255)
    destination = models.CharField(max_length=255)
    referer_hash = models.CharField(max_length=40)
    created = models.DateTimeField()

    def get_destination(self):
        if self.destination and len(self.destination) > 80:
            return '%s...' % self.destination[:80]
        return self.destination

    def get_url(self):
        u = '%s/r/%s/' % (settings.APP_URL, self.url)
        return u

    def total_clicks(self):
        return RefererURLClick.objects.filter(referer_url=self).aggregate(Count('id'))['id__count']

    def total_signups(self):
        return Company.objects.filter(referer_url=self).aggregate(Count('id'))['id__count']


class RefererURLClick(models.Model):
    referer_url = models.ForeignKey(RefererURL, on_delete=models.CASCADE)
    created = models.DateTimeField()


class Referer(models.Model):
    created = models.DateTimeField()
    hash = models.CharField(max_length=40)

    def referer_vars(self):
        return RefererVar.objects.filter(referer=self).order_by('name')


class RefererVar(models.Model):
    referer = models.ForeignKey(Referer, on_delete=models.CASCADE)
    name = models.CharField(max_length=32)
    content = models.TextField()

    def content_pretty(self):
        if self.name == 'q':
            return self.content.replace('+', ' ').replace('%20', ' ')
        return self.content

    def name_pretty(self):
        return self.name.replace('_', ' ')


class DealerStore(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=255)
    address = models.CharField(max_length=80, null=True, blank=True)
    city = models.CharField(max_length=64, null=True, blank=True)
    state = models.ForeignKey(State, on_delete=models.SET_NULL, null=True, blank=True)
    zip = models.CharField(max_length=10, null=True, blank=True)
    country = models.ForeignKey(Country, on_delete=models.SET_NULL, null=True, blank=True)
    latitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)
    longitude = models.DecimalField(max_digits=11, decimal_places=7, null=True, blank=True)

    def __str__(self):
        return '%s' % self.name

    def get_store_phones(self):
        return DealerStorePhone.objects.filter(dealer_store=self).order_by('phone_number')


class ContactStore(models.Model):
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    store = models.ForeignKey(DealerStore, on_delete=models.CASCADE)
    created = models.DateTimeField()


class DealerStorePhone(models.Model):
    dealer_store = models.ForeignKey(DealerStore, on_delete=models.CASCADE)
    phone_type = models.ForeignKey(PhoneType, on_delete=models.CASCADE)
    phone_number = models.CharField(max_length=10)
    ext = models.CharField(max_length=4, null=True, blank=True)
    country_code = models.CharField(max_length=4)
    primary_number = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s %s' % (self.dealer_store.name, self.phone_number)

    def storewithphone(self):
        return '%s (%s)' % (self.dealer_store.name, self.phone_number)

    def autotext(self):
        at = Autotext.objects.filter(store_phone=self).first()
        return at

    def can_spoof(self):
        tcid = TwilioCallerID.objects.filter(dealer_store_phone=self).first()
        if tcid and tcid.status == 'Success' or tcid and tcid.status == 'success':
            return True
        return False


class Beacon(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    store = models.ForeignKey(DealerStore, on_delete=models.CASCADE)
    name = models.CharField(max_length=200)
    uuid = models.CharField(max_length=255)
    minornumber = models.CharField(max_length=20)
    majornumber = models.CharField(max_length=20)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s' % self.name


class Representativetimesheet(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    store = models.ForeignKey(DealerStore, on_delete=models.CASCADE)
    duration = models.IntegerField()
    startdate = models.DateTimeField()
    enddate = models.DateTimeField()
    type = models.CharField(max_length=12)
    timezone = models.CharField(max_length=250)
    device_startdatetime = models.CharField(max_length=25)
    device_enddatetime = models.CharField(max_length=25)
    device = models.CharField(max_length=255, null=True, blank=True)
    beacon_range_available = models.BooleanField(default=True)
    is_in_network = models.BooleanField(default=True)
    battery_percentage = models.CharField(max_length=25)
    device_detail = models.CharField(max_length=250, null=True, blank=True)


class Misscalllog(models.Model):
    user = models.IntegerField()
    caller = models.CharField(max_length=12)
    misscall_count = models.IntegerField()
    is_viewed = models.BooleanField(blank=True, default=None)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class TwilioPhoneNumber(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    tollfree = models.NullBooleanField(null=True, blank=True)
    sid = models.CharField(max_length=48)
    phone_number = models.CharField(max_length=10)
    forward = models.BooleanField(default=False)
    forward_user_phone = models.ForeignKey(UserPhone,
                                           null=True,
                                           blank=True,
                                           on_delete=models.SET_NULL)
    forward_dealer_store_phone = models.ForeignKey(DealerStorePhone,
                                                   null=True,
                                                   blank=True,
                                                   on_delete=models.SET_NULL)
    forward_client = models.TextField(null=True, blank=True)
    forward_phone_number = models.CharField(max_length=10, null=True, blank=True)
    record = models.BooleanField(default=False)
    deactivated = models.BooleanField(default=False)
    deactivated_date = models.DateTimeField(null=True, blank=True)
    deleted = models.BooleanField(default=False)
    deleted_date = models.DateTimeField(null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    client_initials = models.BooleanField(default=False, blank=True)
    is_forward_client = models.BooleanField(default=False, blank=True)
    country_code = models.CharField(max_length=4, default=None)
    forward_to_default_salesrep = models.BooleanField(default=False, blank=True)
    forward_to_carrier = models.BooleanField(default=False, blank=True)
    carrier_ids = models.CharField(max_length=250, null=True, blank=True)
    forward_to_carrier_number = models.CharField(max_length=10, null=True, blank=True)
    forward_to_non_carrier_number = models.CharField(max_length=10, null=True, blank=True)
    country_code_carrier = models.CharField(max_length=4, default=None)
    country_code_without_carrier = models.CharField(max_length=4, default=None)
    is_forward_call_center = models.BooleanField(default=False, blank=True)
    call_center_ids = models.CharField(max_length=250, null=True, blank=True)
    voicemail_callsid = models.CharField(max_length=48)
    voicemail_url = models.CharField(max_length=255, null=True, blank=True)
    voicemail_status = models.CharField(max_length=16, null=True, blank=True)
    duration = models.IntegerField(null=True, blank=True, default=0)
    voicemail = models.BooleanField(default=False, blank=True)
    is_autotext = models.BooleanField(default=False, blank=True)
    msg = models.CharField(max_length=140)
    missed_call_notification = models.BooleanField(default=False, blank=True)
    user_email_missed_call_notification = models.CharField(max_length=255, null=True, blank=True)
    is_forward_sip = models.BooleanField(default=False, blank=True)
    sip_names = models.TextField(null=True, blank=True)
    beacon_id = models.IntegerField(null=True, blank=True)
    campaign = models.CharField(max_length=255, null=True, blank=True)
    message_sid = models.CharField(max_length=255, null=True, blank=True)

    def __str__(self):
        return '%s %s' % (self.company.name, self.phone_number)

    def autotext(self):
        atp = AutotextTwilioPhone.objects.filter(twilio_phone=self).first()
        if atp:
            return atp.autotext

    def active(self):
        return not self.deactivated

    def recording_url(self):
        try:
            if 'https://' in self.voicemail_url:
                return self.voicemail_url
            if 'http://' in self.voicemail_url:
                return self.voicemail_url.replace('http://', 'https://')
            if self.voicemail_url:
                return '%s%s' % (settings.VOICEMAIL_GREETINGS_URL, self.voicemail_url)
        except:
            pass
        return ''

    def get_dealer_store_phone(self):
        return DealerStorePhone.objects.filter(phone_number=self.phone_number).first()

    def get_call_summary_notification(self):
        return CallSummarySettings.objects.filter(twilio_phone=self).first()


class TwilioPhoneSMSEmail(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    twilio_phone = models.ForeignKey(TwilioPhoneNumber, on_delete=models.CASCADE)


class FollowupCall(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    followup = models.ForeignKey(Followup, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    store = models.ForeignKey('DealerStore', on_delete=models.SET_NULL, null=True, blank=True)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    contact_phone = models.ForeignKey(ContactPhone, on_delete=models.CASCADE)
    call = models.ForeignKey(Call, null=True, blank=True, on_delete=models.SET_NULL)
    twilio_call = models.ForeignKey(TwilioCall, null=True, blank=True, on_delete=models.SET_NULL)
    response_time = models.DecimalField(max_digits=6, decimal_places=2)
    new_upgrade = models.BooleanField(default=False)
    upgrade_time = models.DecimalField(max_digits=6, decimal_places=2, null=True, blank=True)
    created = models.DateTimeField()
    is_followup_call = models.BooleanField(default=True)

    def __str__(self):
        return '%s %s %s' % (self.user.first_name, self.user.last_name, self.contact)


class StatFollowupCallDaily(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    store = models.ForeignKey('DealerStore', on_delete=models.SET_NULL, null=True, blank=True)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    date = models.DateField()
    count = models.IntegerField()
    upgrade_count = models.IntegerField()
    response_time = models.DecimalField(max_digits=6, decimal_places=2)
    upgrade_time = models.DecimalField(max_digits=6, decimal_places=2, null=True, blank=True)


class StatFollowupCallMonthly(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    store = models.ForeignKey('DealerStore', on_delete=models.SET_NULL, null=True, blank=True)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    year = models.IntegerField()
    month = models.IntegerField()
    calls_count = models.IntegerField(default=0)
    calls_count_rank = models.IntegerField(default=0)
    upgrade_calls_count = models.IntegerField(default=0)
    succ_upgrade_calls_rank = models.IntegerField(default=0)
    succ_upgrade_calls_count = models.IntegerField(default=0)
    upgrade_calls_rank = models.IntegerField(default=0)
    closing_percentage = models.IntegerField(default=0)
    closing_percentage_rank = models.IntegerField(default=0)
    profit_per_call = models.DecimalField(max_digits=6, decimal_places=2, default=0)
    profit_per_call_rank = models.IntegerField(default=0)
    response_time = models.DecimalField(max_digits=6, decimal_places=2, default=0)
    response_time_rank = models.IntegerField(default=0)
    upgrade_time = models.DecimalField(max_digits=6, decimal_places=2, default=0)
    upgrade_time_rank = models.IntegerField(default=0)


class DuplicateRun(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    running = models.BooleanField(default=False)
    done = models.BooleanField(default=False)
    updated = models.DateTimeField()
    created = models.DateTimeField()


class DuplicateFilterOptions(models.Model):
    key = models.CharField(max_length=256)
    name = models.CharField(max_length=256)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class DuplicateContact(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    duplicate = models.ForeignKey(Contact, related_name='duplicate', on_delete=models.CASCADE)
    never_merge = models.BooleanField(default=False)
    filter = models.ForeignKey(DuplicateFilterOptions, on_delete=models.CASCADE, null=True, blank=True)


class DuplicateContactCompany(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_company = models.ForeignKey(ContactCompany, on_delete=models.CASCADE)
    duplicate = models.ForeignKey(ContactCompany,
                                  related_name='duplicate',
                                  on_delete=models.CASCADE)
    never_merge = models.BooleanField(default=False)


class Report(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    days = models.IntegerField()
    days_offset = models.IntegerField(default=0)
    rcalls = models.BooleanField(default=False)
    rcalls_group_by = models.BooleanField(default=False)
    rcalls_incoming = models.BooleanField(default=True)
    rcalls_combine = models.BooleanField(default=False)
    r_events = models.BooleanField(default=False)
    by_market = models.BooleanField(default=False)
    repassigns = models.BooleanField(default=False)
    position = models.IntegerField()
    date_mode = models.IntegerField()
    first_day = models.IntegerField()
    static_type = models.IntegerField()
    archived = models.BooleanField(default=False)
    schedule = models.IntegerField(default=0)  # 0 weekly, 1 monthly
    show_all_eforms = models.BooleanField(default=False)
    next_week_followup_ids = models.TextField()
    scheduled_days = models.IntegerField()
    show_past_appt = models.BooleanField(default=False)
    previous_month_report = models.BooleanField(default=False)
    previous_week_report = models.BooleanField(default=False)

    def notifications(self):
        emails = ''
        for rem in ReportEMail.objects.filter(report=self):
            emails += '%s\n' % rem.email
        return emails

    def requested(self):
        rr = ReportRequest.objects.filter(report=self).first()
        return True if rr else False

    def last_report_email_hash(self):
        e = Email.objects.filter(report=self).order_by('-id').first()
        if e:
            return e.hashed
        return ''

    def last_report_name(self):
        e = Email.objects.filter(report=self).order_by('-id').first()
        if e:
            fa = EmailFileAttachment.objects.filter(email=e).first()
            if fa:
                return fa
        return ''


class ReportRequest(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    report = models.ForeignKey(Report, on_delete=models.CASCADE)
    created = models.DateTimeField()


class ReportRecipient(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    report = models.ForeignKey(Report, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)


class ReportEMail(models.Model):
    report = models.ForeignKey(Report, on_delete=models.CASCADE)
    email = models.CharField(max_length=64)

    def __str__(self):
        return '%s %s' % (self.report.name, self.email)


class ReportSalesRep(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    report = models.ForeignKey(Report, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)


class ReportSendDay(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    report = models.ForeignKey(Report, on_delete=models.CASCADE)
    day = models.IntegerField()


class ReportFieldAction(models.Model):
    name = models.CharField(max_length=64)


class ReportField(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    report = models.ForeignKey(Report, on_delete=models.CASCADE)
    event_form = models.ForeignKey(EventForm, on_delete=models.CASCADE)
    event_form_cfield = models.ForeignKey(EventFormCField,
                                          null=True,
                                          blank=True,
                                          on_delete=models.SET_NULL)
    count_entries = models.BooleanField(default=True)
    report_field_action = models.ForeignKey(ReportFieldAction,
                                            null=True,
                                            blank=True,
                                            on_delete=models.SET_NULL)
    group_by = models.NullBooleanField()
    position = models.IntegerField()


class ReportFieldGroupBy(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    report_field = models.ForeignKey(ReportField, on_delete=models.CASCADE)
    cfield_option = models.ForeignKey(CFieldOption, on_delete=models.CASCADE)


class ReportCallResultGroupBy(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    report = models.ForeignKey(Report, on_delete=models.CASCADE)
    call_result = models.ForeignKey(TwilioCallResult, on_delete=models.CASCADE)


class ReportEventType(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    report = models.ForeignKey(Report, on_delete=models.CASCADE)
    event_type = models.ForeignKey(EventType, on_delete=models.CASCADE)


class ReportMarket(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    report = models.ForeignKey(Report, on_delete=models.CASCADE)
    market = models.ForeignKey(Market, on_delete=models.CASCADE)


# top level
class Menu(models.Model):
    name = models.CharField(max_length=64)
    url = models.CharField(max_length=128, default='')
    position = models.IntegerField(default=0)
    css_class = models.CharField(max_length=6, default='')
    anon = models.BooleanField(default=False)
    manager = models.BooleanField(default=False)


class MenuCol(models.Model):
    menu = models.ForeignKey(Menu, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    position = models.IntegerField(default=0)
    anon = models.BooleanField(default=False)
    manager = models.BooleanField(default=False)

    def get_name(self):
        if len(self.name) == 0:
            return 'col %s' % self.position
        return self.name


class MenuRow(models.Model):
    menu_col = models.ForeignKey(MenuCol, on_delete=models.CASCADE)
    name = models.CharField(max_length=64, default='')
    position = models.IntegerField(default=0)
    anon = models.BooleanField(default=False)
    manager = models.BooleanField(default=False)

    def get_name(self):
        if len(self.name) == 0:
            return 'row %s' % self.position
        return self.name

    def get_next_pos(self):
        pos = 0
        url = MenuURL.objects.filter(menu_row=self).order_by('-position').first()
        if url:
            pos = url.position + 1
        return pos

    @staticmethod
    def get_opts(selected_id=None):
        opts = []

        for m in Menu.objects.order_by('position'):
            for c in MenuCol.objects.filter(menu_id=m.id).order_by('position'):
                for r in MenuRow.objects.filter(menu_col_id=c.id).order_by('position'):
                    n = '%s &#187; %s &#187; %s' % (m.name, c.get_name(), r.get_name())
                    selected = ' selected="selected"' if r.id == selected_id else ''
                    opts.append('<option value="%s"%s>%s</option>' % (r.id, selected, n))

        return '\n'.join(opts)


class MenuURL(models.Model):
    menu_row = models.ForeignKey(MenuRow, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    url = models.CharField(max_length=128, default='')
    cost = models.IntegerField(default=0)
    position = models.IntegerField(default=0)
    anon = models.BooleanField(default=False)
    manager = models.BooleanField(default=False)
    tools = models.BooleanField(default=False)
    twilio = models.BooleanField(default=False)
    dealer = models.BooleanField(default=False)


class MenuCust(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    menu = models.ForeignKey(Menu, on_delete=models.CASCADE)
    name = models.CharField(max_length=64, default='')
    hide = models.BooleanField(default=False)
    cost = models.IntegerField(default=0)


class MenuColCust(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    menu_col = models.ForeignKey(MenuCol, on_delete=models.CASCADE)
    name = models.CharField(max_length=64, default='')
    hide = models.BooleanField(default=False)
    cost = models.IntegerField(default=0)


class MenuRowCust(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    menu_row = models.ForeignKey(MenuRow, on_delete=models.CASCADE)
    name = models.CharField(max_length=64, default='')
    hide = models.BooleanField(default=False)
    cost = models.IntegerField(default=0)


class MenuURLCust(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    menu_url = models.ForeignKey(MenuURL, on_delete=models.CASCADE)
    name = models.CharField(max_length=64, default='')
    hide = models.BooleanField(default=False)
    cost = models.IntegerField(default=0)


class ContactListCust(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_name = models.CharField(max_length=100, default='')
    company_name = models.CharField(max_length=100, default='')
    address = models.CharField(max_length=100, default='')
    phone_distance = models.CharField(max_length=100, default='')
    contacted = models.CharField(max_length=100, default='')
    sales_rep = models.CharField(max_length=100, default='')
    last_appointment = models.CharField(max_length=100, default='')


class RankGroup(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)
    date_mode = models.IntegerField(default=0)  # 0 = rolling, 1 = midnight
    first_day = models.IntegerField(default=6)  # 6 = Sunday, 0 = Monday
    last = models.DateTimeField()

    def current_rank_users(self, rank_type):
        return RankUser.objects.filter(company=self.company,
                                       rank_group=self,
                                       rank_type=rank_type,
                                       date=self.last).order_by('rank')

    def date_mode_name(self):
        return 'Rolling' if self.date_mode == 0 else 'Static'

    def first_day_name(self):
        return 'Monday' if self.first_day == 0 else 'Sunday'

    def get_sales_reps(self):
        sql = """
            SELECT 
                auth_user.id AS id, 
                auth_user.first_name, 
                auth_user.last_name
            FROM auth_user
                LEFT JOIN cp_rankgroupuser
                    ON auth_user.id = cp_rankgroupuser.user_id
                LEFT JOIN cp_userprofile
                    ON auth_user.id = cp_userprofile.user_id
            WHERE
                cp_rankgroupuser.rank_group_id = %s
                AND cp_userprofile.company_id = %s
            ORDER BY auth_user.first_name
        """ % (self.id, self.company_id)

        return list(User.objects.raw(sql))


class RankGroupUser(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    rank_group = models.ForeignKey(RankGroup, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)


class RankType(models.Model):
    name = models.CharField(max_length=64)


class RankUser(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    rank_group = models.ForeignKey(RankGroup, on_delete=models.CASCADE)
    rank_type = models.ForeignKey(RankType, on_delete=models.CASCADE)
    date = models.DateTimeField()
    points = models.IntegerField(default=0)
    rank = models.IntegerField(default=0)

    def trend_img(self):
        img = '&nbsp;'
        now = timezone.localtime(timezone.now())

        if self.rank_type.name == 'day':
            days = now - timedelta(days=1)
        elif self.rank_type.name == 'week':
            days = now - timedelta(days=7)
        elif self.rank_type.name == 'month':
            days = now - timedelta(days=30)

        prev = RankUser.objects.filter(company=self.company,
                                       user=self.user,
                                       rank_group=self.rank_group,
                                       rank_type=self.rank_type,
                                       date__lt=days).order_by('-date').first()
        if prev:
            if prev.rank > self.rank:
                img = '<img src="%s/images/trend_up.png" title="" alt="" />' % settings.MEDIA_URL
            elif prev.rank < self.rank:
                img = '<img src="%s/images/trend_down.png" title="" alt="" />' % settings.MEDIA_URL
        return img


class ExportType(models.Model):
    name = models.CharField(max_length=64)

    def __str__(self):
        return '%s' % self.name


class ExportRun(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    export_type = models.ForeignKey(ExportType, on_delete=models.CASCADE)
    session = models.CharField(max_length=32768)
    filename = models.CharField(max_length=64, null=True, blank=True)
    running = models.BooleanField(default=False)
    done = models.BooleanField(default=False)
    updated = models.DateTimeField()
    created = models.DateTimeField()

    def get_email(self):
        return Email.objects.filter(export_run=self).first()

    def pretty_name(self):
        n = self.export_type.name
        return '%s' % n.replace('_id', '').replace('_', ' ').title()


def update_company_last_activity(sender, instance, **kwargs):
    if kwargs.get('created') and not instance.user.userprofile.is_support():
        if instance.created > instance.company.last_activity:
            instance.company.last_activity = instance.created
            instance.company.save()


post_save.connect(update_company_last_activity,
                  sender=ExportRun,
                  dispatch_uid="update_company_last_activity")


class UserGoogleCal(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    item_id = models.CharField(max_length=255)
    summary = models.CharField(max_length=255)
    tz = models.CharField(max_length=64)

    def name(self):
        return self.summary


class UserOfficeCal(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    item_id = models.CharField(max_length=255)
    summary = models.CharField(max_length=255)

    def name(self):
        return self.summary


class Autotext(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    store = models.ForeignKey(DealerStore, on_delete=models.CASCADE)
    store_phone = models.ForeignKey(DealerStorePhone, on_delete=models.CASCADE)

    vm_count = models.IntegerField(default=0)
    sms_count = models.IntegerField(default=0)

    deleted = models.BooleanField(default=False)
    deleted_date = models.DateTimeField(null=True, blank=True)

    created = models.DateTimeField()
    updated = models.DateTimeField()

    def __str__(self):
        return '%s %s' % (self.company.name, self.store.name)

    def greeting(self):
        return AutotextGreeting.objects.filter(company=self.company, autotext=self).first()

    def public_twilio_phone(self):
        aptp = AutotextPublicTwilioPhone.objects.filter(company=self.company, autotext=self).first()
        if aptp:
            return aptp.twilio_phone
        return None

    def twilio_phone(self):
        atp = AutotextTwilioPhone.objects.filter(company=self.company, autotext=self).first()
        if atp:
            return atp.twilio_phone
        return None

    def sms_msgs(self):
        msgs = []
        for m in AutotextSMSMessage.objects.filter(company=self.company,
                                                   autotext=self).order_by('id'):
            msgs.append(m.msg)
        return msgs

    def vm_recipients(self):
        emails = []
        for e in AutotextVMEmail.objects.filter(company=self.company, autotext=self):
            emails.append(e.email)
        return emails

    def vm_recipients_count(self):
        return len(self.vm_recipients())

    def vm_recipients_list(self):
        return ', '.join(self.vm_recipients())

    def sms_recipients(self):
        emails = []
        for e in AutotextSMSEmail.objects.filter(company=self.company, autotext=self):
            emails.append(e.email)
        return emails

    def sms_recipients_list(self):
        return ', '.join(self.sms_recipients())

    def sms_recipients_count(self):
        return len(self.sms_recipients())


class AutotextPublicTwilioPhone(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    autotext = models.ForeignKey(Autotext, on_delete=models.CASCADE)
    twilio_phone = models.ForeignKey(TwilioPhoneNumber, on_delete=models.CASCADE)


class AutotextTwilioPhone(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    autotext = models.ForeignKey(Autotext, on_delete=models.CASCADE)
    twilio_phone = models.ForeignKey(TwilioPhoneNumber, on_delete=models.CASCADE)


class AutotextSMSMessage(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    autotext = models.ForeignKey(Autotext, on_delete=models.CASCADE)
    msg = models.CharField(max_length=140)


class AutotextVMEmail(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    autotext = models.ForeignKey(Autotext, on_delete=models.CASCADE)
    email = models.CharField(max_length=64)


class AutotextSMSEmail(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    autotext = models.ForeignKey(Autotext, on_delete=models.CASCADE)
    email = models.CharField(max_length=64)


class AutotextGreeting(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    autotext = models.ForeignKey(Autotext, on_delete=models.CASCADE)
    call_sid = models.CharField(max_length=48)
    url = models.CharField(max_length=255, null=True, blank=True)
    call_status = models.CharField(max_length=16, null=True, blank=True)
    duration = models.IntegerField(null=True, blank=True, default=0)
    deleted = models.BooleanField(default=False)
    created = models.DateTimeField()

    def recording_url(self):
        if self.url is None:
            return ''
        elif 'https://' in self.url:
            return self.url
        elif 'http://' in self.url:
            return self.url.replace('http://', 'https://')
        elif self.url:
            return '%s%s' % (settings.AUTOTEXT_GREETINGS_URL, self.url)

    def status(self):
        from home.templatetags.home_extras import formatted_phone_number
        status = 'Unknown'
        up = self.user.userprofile
        phone_number = formatted_phone_number(up.default_phone.phone_number)

        if self.duration in [0, 1]:
            status = 'Calling <b>%s</b>' % phone_number
        else:
            status = 'Call has ended: <b>%s</b>' % self.call_status.title()
        return status


class Page(models.Model):
    name = models.CharField(max_length=64)


class PageVisit(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    page = models.ForeignKey(Page, on_delete=models.CASCADE)
    created = models.DateTimeField()


class EmailProtocol(models.Model):
    name = models.CharField(max_length=8)

    def __str__(self):
        return '%s' % self.name


class EmailAccount(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    protocol = models.ForeignKey(EmailProtocol, on_delete=models.CASCADE)
    address = models.CharField(max_length=80)  # Email address of the user
    hostname = models.CharField(max_length=80)
    port = models.IntegerField()
    username = models.CharField(max_length=80)
    passwd = models.CharField(max_length=80)
    last_checked = models.DateTimeField(null=True, blank=True)  # 2021-03-04 MT: deprecating soon
    disabled = models.BooleanField(default=False)
    deleted = models.BooleanField(default=False)
    passwd_failing = models.BooleanField(default=False)
    failed_count = models.IntegerField(default=0)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    oauth_refresh_token = models.TextField()
    sent_mail_count = models.IntegerField(default=0)
    fetch_mail_version = models.IntegerField(default=2)

    # Date the credentials (password or oauth_refresh_token) were last updated.
    credentials_updated_datetime = models.DateTimeField(null=True)

    # Dates of the most recent synchronization: attempt, successful and failed attempts.
    #   If a value is null, then it hasn't been attempted yet.
    most_recent_sync_attempt_datetime = models.DateTimeField(null=True)
    most_recent_sync_successful_datetime = models.DateTimeField(null=True)
    most_recent_sync_failed_datetime = models.DateTimeField(null=True)

    # If a mailbox is failing, when did it start failing? Otherwise, this should be null.
    sync_first_started_failing_datetime = models.DateTimeField(null=True)

    # Target date to synchronize mailbox data locally.
    #   In the future, we might want to set a default of: default=datetime.date(2020, 1, 1)
    target_sync_to_date = models.DateField(null=True)

    # Start and end dates which identify the range of emails which have been synced locally.
    #   This also identifies where we should start syncing data for the user if the
    #   mailbox connection started failing and the credentials were updated.
    synced_to_start_date = models.DateField(null=True)
    synced_to_end_date = models.DateField(null=True)

    # Total number of emails downloaded and number of bytes downloaded
    emails_downloaded_count = models.BigIntegerField(default=0)
    emails_downloaded_bytes = models.BigIntegerField(default=0)

    # DateTime the last authentication failure notification email was sent.
    #   This field is used to determine if another notification email should be sent.
    last_failed_auth_notification_email_datetime = models.DateTimeField(null=True)

    # Date this mailbox was disabled or deleted. Should be null if those values are not set.
    disabled_datetime = models.DateTimeField(null=True)
    deleted_datetime = models.DateTimeField(null=True)

    # These fields are used to determine the details about the historical sync
    historical_sync_scheduled_date = models.DateTimeField(null=True)
    historical_sync_start_date = models.DateField(null=True)
    historical_sync_frequency = models.CharField(max_length=80, null=True)
    last_historical_sync_date = models.DateTimeField(null=True)

    def is_gmail(self) -> bool:
        return str(self.hostname).find("gmail") >= 0

    def is_office(self) -> bool:
        return str(self.hostname).find("office365") >= 0

    # Does this object use Google OAuth to connect?
    def is_using_google_oauth(self) -> bool:
        return self.hostname.find('gmail.com') > 1 and \
               self.oauth_refresh_token != '' and \
               self.oauth_refresh_token is not None

    # Does this object use Microsoft OAuth to connect?
    def is_using_office365_oauth(self) -> bool:
        return self.hostname.find('office365.com') > 1 and \
               self.oauth_refresh_token != '' and \
               self.oauth_refresh_token is not None

    # Verify that this email account is a valid target for synchronizing email
    def is_valid_sync_target(self):
        if self.company.disabled:
            logger.debug(f"emailAccount.company.disabled: {self.company.disabled}")
            return False

        if not self.company.check_email:
            logger.debug(f"emailAccount.company.check_email: {self.company.check_email}")
            return False

        if self.disabled:
            logger.debug(f"emailAccount.disabled: {self.disabled}")
            return

        if self.deleted:
            logger.debug(f"emailAccount.deleted: {self.deleted}")
            return

        if self.passwd_failing and self.failed_count > EmailAccount.max_failed_count():
            logger.debug(f"emailAccount.passwd_failing: {self.passwd_failing}")
            logger.debug(f"emailAccount.failed_count: {self.failed_count}")
            return False

        # If the mailbox owner is disabled, then treat the mailbox as disabled
        account_disabled_setting = UserSetting.objects \
            .filter(user=self.user, name='account_disabled').first()
        if account_disabled_setting and account_disabled_setting.value == '1':
            logger.debug("account_disabled flag: %s" % account_disabled_setting.value)
            return False
        return True

    @staticmethod
    def max_failed_count():
        return 4

    @staticmethod
    def make_passwd(passwd='changeme'):
        iv = Crypto.Random.get_random_bytes(AES.block_size)
        cipher = AES.new(get_email_crypt_key(), AES.MODE_CFB, iv)
        encrypted_password = cipher.encrypt(passwd.encode('utf-8'))
        return (iv + encrypted_password).hex()

    def __str__(self):
        return '%s' % self.address

    def get_last_checked(self):
        if self.last_checked:
            lc = self.last_checked - timedelta(days=1)
        else:
            lc = timezone.localtime(timezone.now()) - timedelta(days=30)
        return lc.strftime('%d-%b-%Y')

    def get_iv(self):
        return self.passwd[:16]
        # return self.passwd[:32].decode( 'hex' )

    def get_passwd(self):
        if not self.passwd:
            return ''
        iv = self.get_iv()
        iv = bytes(iv, 'utf-8') if isinstance(iv, str) else iv

        new_crypt = get_email_crypt_key()
        new_crypt = bytes(new_crypt, 'utf-8') if isinstance(new_crypt, str) else new_crypt

        cipher = AES.new(new_crypt, AES.MODE_CFB, iv)
        passwd = bytes.fromhex(self.passwd) if isinstance(self.passwd, str) else self.passwd
        return cipher.decrypt(passwd)[len(iv):].decode("utf-8")
        # return cipher.decrypt( self.passwd.decode( 'hex' ) )[len( iv ):]

    def oauth2_sync_imap4_login(self, auth_string=''):
        # - Gmail oauth2 code
        try:
            imap_conn = imaplib.IMAP4_SSL('imap.gmail.com')
            imap_conn.debug = 0  # - no print
            imap_conn.authenticate('XOAUTH2', lambda x: auth_string)
            return imap_conn
        except:
            return False

    def save_sync_imap4_folders(self, folders):
        names = []
        now = timezone.localtime(timezone.now())
        try:
            labels = folders['labels']
            for f in labels:
                name = f['id']
                pretty_name = f['name']
                if name == GMAIL_ROOT_FOLDER:
                    # Skip gmail root folder
                    continue
                names.append(name)
                imf = ImapFolder.objects.filter(company=self.company,
                                                user=self.user,
                                                account=self,
                                                name=name).first()

                if imf is None:
                    imf = ImapFolder(company=self.company,
                                     user=self.user,
                                     account=self,
                                     name=name,
                                     pretty_name=pretty_name,
                                     created=now)
                    for fn in ['inbox', 'sent', ]:
                        if name.lower().find(fn) > -1:
                            imf.check = True
                    try:
                        imf.save()
                    except:
                        pass
        except:
            return {'error': 'Unable to save folders'}
        try:
            for imf in ImapFolder.objects.filter(company=self.company,
                                                 user=self.user,
                                                 account=self):
                if imf.name not in names:
                    imf.delete()
        except:
            return {'error': 'Fail in deleting the previous folders'}
        return {'success': 'Sync Successfully'}

    def save_other_folders(self, folders):
        now = timezone.localtime(timezone.now())

        for f in folders:
            if isinstance(f, bytes):
                f = f.decode()
            try:
                name = shlex.split(f)
                if name:
                    name = name[-1]
            except AttributeError:
                # getting 'tuple' object has no attribute 'read' error thats why its continue
                continue
            except:
                logger.error("Error in other provider email sync. EmailAccount: %s",
                             self.id,
                             exc_info=sys.exc_info())
                return {'error': 'Unable to sync folders.'}

            if name:
                if name == GMAIL_ROOT_FOLDER:
                    # Skip gmail root folder
                    continue

                imf = ImapFolder.objects.filter(company=self.company,
                                                user=self.user,
                                                account=self,
                                                name=name)[:1]

                if not imf.exists():
                    imf = ImapFolder(company=self.company,
                                     user=self.user,
                                     account=self,
                                     name=name,
                                     pretty_name=name,
                                     created=now)
                    imf.save()
        return {'success': 'Sync Successfully'}

    def sync_imap4_folders(self):
        if not self.company.check_email:
            return {'error': 'Mail check failed'}

        if self.passwd_failing and self.failed_count > EmailAccount.max_failed_count():
            return {'error': 'Maximum attempt'}

        if self.deleted:
            return {'error': 'Object Expire'}

        if self.disabled:
            return {'error': 'Object Disable'}

        maillog('\n**** Getting IMAP4 Folders ****')
        maillog('h: %s' % self.hostname)
        maillog('u: %s' % self.username)

        try:
            mb = imaplib.IMAP4_SSL(self.hostname, self.port)
        except:
            mb = None

        maillog('mb: %s' % mb)

        if mb is None:
            maillog('IMAP4 mailbox connection failed')
            return {'error': 'IMAP4 mailbox connection failed'}

        try:
            l = mb.login(self.username, self.get_passwd())[0]
        except:
            return {'error': 'Login failed'}

        maillog('l: %s' % l)

        if l != 'OK':
            maillog('IMAP4 login failed')
            return {'error': 'IMAP4 login failed'}

        try:
            folders = mb.list()[1]
        except:
            folders = []

        try:
            mb.logout()
        except:
            pass

        return {'success': 'IMAP login success', 'folders': folders}

    def password_fail(self):
        if self.failed_count == 0:
            self.sync_first_started_failing_datetime = timezone.localtime(timezone.now())
        self.passwd_failing = True
        self.failed_count += 1
        self.last_checked = timezone.localtime(timezone.now())
        self.most_recent_sync_failed_datetime = timezone.localtime(timezone.now())
        self.save()

    def password_success(self):
        if self.passwd_failing:
            self.most_recent_sync_failed_datetime = None
            self.sync_first_started_failing_datetime = None
            self.last_failed_auth_notification_email_datetime = None
            self.passwd_failing = False
            self.failed_count = 0
            self.sent_mail_count = 0
            self.save()

    def sync_attempt_started(self):
        self.most_recent_sync_attempt_datetime = timezone.localtime(timezone.now())
        self.save()

    def sync_completed_success(self, emails_downloaded_count: int = 0):
        self.emails_downloaded_count = emails_downloaded_count
        self.last_checked = timezone.localtime(timezone.now())
        self.most_recent_sync_successful_datetime = timezone.localtime(timezone.now())
        self.synced_to_end_date = date.today()
        if self.historical_sync_start_date:
            self.historical_sync_start_date = None
            self.last_historical_sync_date = timezone.localtime(timezone.now())
        self.save()

    def make_login(self):
        maillog('make_login')
        # Attempt to connect to the target mailbox using an IMAP4 username & password
        if self.oauth_refresh_token is None or self.oauth_refresh_token == '':
            try:
                self.sync_imap4_folders()
            except:
                pass

            try:
                mb = imaplib.IMAP4_SSL(self.hostname, self.port)
            except:
                mb = None

            maillog('mb: %s' % mb)

            if mb is None:
                maillog('IMAP4 mailbox connection failed')
                return False

            try:
                login_response = mb.login(self.username, self.get_passwd())[0]
            except:
                login_response = None

            maillog('login_response: %s' % login_response)

            if login_response != 'OK':
                maillog('IMAP4 login failed')
                self.password_fail()
                return False

            self.password_success()
            return mb

        # Retrieve an access_token using the refresh_token
        response = em.oauth2.RefreshToken(self.oauth_refresh_token)
        try:
            if response['access_token']:
                auth_string = em.oauth2.GenerateOAuth2String(self.username,
                                                             response['access_token'],
                                                             base64_encode=False)
                mb = self.oauth2_sync_imap4_login(auth_string)
                if not mb:
                    maillog('IMAP4 mailbox connection failed')
                    logger.error('Fetch Mail Cron Job Error,imap connection failed Acc ID: %s,exc_info: %s',
                                 self.id,
                                 exc_info=sys.exc_info())
                    self.password_fail()
                    return False
                self.password_success()
                return mb
        except Exception as e:
            logger.error('Fetch Mail Cron Job Error Acc ID: %s,exc_info: %s',
                         self.id, e,
                         exc_info=sys.exc_info())
            self.password_fail()
            return False

    def save_message(self, from_, all_recipients_, subject, email_msg, message_id, date_, ext_dtl, type='imap'):
        # WARN: The type = 'imap' is not necessarily correct because it's also used for
        #   processing emails that are received via the Gmail API.

        # holds the cp_contact record that this email is related to
        # This represents a Customer Account record within a CallProof Customer
        contact = None

        # Boolean that represents whether the user sent or received this email.
        is_received_email = (not from_ == self.address.strip().lower())

        # Attempt to identify a single Contact to attach this record to
        # FUTURE: This should be refactored to a separate set of functions
        #   which would be used to identify the primary cp_contact record
        #   related to this email
        if is_received_email:
            # search ContactPersonnel in this cp_company by From:
            try:
                cps = ContactPersonnel.objects \
                    .exclude(email='') \
                    .exclude(email=None) \
                    .filter(company=self.company, email__iexact=from_)[0]
                contact = cps.contact
                logger.debug(f"Contact Found: {contact}")
                if cps.last_contacted is None or cps.last_contacted < date_:
                    cps.last_contacted = date_
                    cps.save()
            except:
                contact = None
        else:
            # search ContactPersonnel in this cp_company by To:
            for to_ in all_recipients_:
                try:
                    cps = ContactPersonnel.objects \
                        .exclude(email='') \
                        .exclude(email=None) \
                        .filter(company=self.company, email__iexact=to_)[0]
                    contact = cps.contact
                    if cps.last_contacted is None or cps.last_contacted < date_:
                        cps.last_contacted = date_
                        cps.save()
                    break
                except:
                    contact = None

        # if we still haven't found the Contact(ie: account),
        #   then this email wasn't sent to or received from a Person in a Contact(account)
        # In this case, we'll search by the Contact records themselves because that
        # effectively represents a company the user is communicating with
        if contact is None:
            if is_received_email:
                # search Contacts in this cp_company by From:
                contacts = Contact.objects \
                    .exclude(email='') \
                    .exclude(email=None) \
                    .filter(company=self.company, email__iexact=from_).first()
            else:
                # search Contacts in this cp_company by To:
                for to_ in all_recipients_:
                    contacts = Contact.objects \
                                   .exclude(email='') \
                                   .exclude(email=None) \
                                   .filter(company=self.company, email__iexact=to_)[:1]
                    try:
                        contact = contacts[0]
                        break  # stop after the first Contact is found
                    except:
                        contact = None

        # If we still haven't been able to find the Contact(account) record,
        #   evaluate the ContactInfoEmail records, because an additional email address
        #   might have been added and would be listed there.
        if contact is None:
            if is_received_email:
                # search ContactInfoEmails in this cp_company by From:
                contact_info_emails = ContactInfoEmail.objects \
                                          .exclude(email='') \
                                          .exclude(email=None) \
                                          .filter(company=self.company, email__iexact=from_)[:1]
                try:
                    contact_info_email = contact_info_emails[0]
                except:
                    contact_info_email = None

                if contact_info_email:
                    contact = contact_info_email.contact
            else:
                # search ContactInfoEmails in this cp_company by To:
                for to_ in all_recipients_:
                    contact_info_emails = ContactInfoEmail.objects \
                                              .exclude(email='') \
                                              .exclude(email=None) \
                                              .filter(company=self.company, email__iexact=to_)[:1]
                    try:
                        contact_info_email = contact_info_emails[0]
                    except:
                        contact_info_email = None

                    if contact_info_email:
                        contact = contact_info_email.contact
                        break

                    if contact:
                        break

        # If we couldn't find a Contact to associate this email with, then don't save it
        if contact is None:
            logger.debug("EXITING: Contact Not found.")
            return

        # Save the email to the database
        logger.debug("Saving email to database...")

        # We need to normalize the message_id here because if this function is called from the API,
        # the message_id might not have been stripped of whitespace
        message_id = message_id.strip()[:255]

        # Build a url_hash where the user can view this message in CP
        # For security purposes, this uses the current time in addition to the message_id
        # so that it cannot be guessed, nor will it be the same from one run to the next.
        s = '%s%s' % (timezone.localtime(timezone.now()), message_id)
        url_hash = hashlib.sha1(str(s).encode('utf-8')).hexdigest()

        # build a pipe-delimited list of email addresses of all of the recipients
        unique_recipients = '|'.join(EmailMsg.parse_unique_recipients(all_recipients_))

        # BUG: This appears to tie each email to a single Contact(cp_contact) in the database.
        #   This is effectively an Account of a Callproof customer.
        #   There's a larger issue here where emails should be available to any of the
        #   accounts, contacts or people where an email address matches. The problem is
        #   that there are permissions issues to consider, so this can't be resolved now.
        #   For the time being, we're going to live with this design flaw, but it's something
        #   that will need to eventually be addressed.
        em = EmailMsg(company=self.company,
                      user=self.user,
                      account=self,
                      contact=contact,
                      contact_type=contact.contact_type,
                      content=email_msg,
                      # text_plain
                      # text_html
                      to_email=unique_recipients,
                      from_email=from_,
                      message_id=message_id,
                      url_hash=url_hash,
                      subject=subject if subject else '',
                      inbox=is_received_email,
                      sent_date=date_,
                      created=timezone.localtime(timezone.now()))
        em_id = None

        try:
            logger.debug(f"saving message...")
            em.save()
            em_id = em.id
            logger.debug(f"EmailMsg.id={em_id}")
        except Exception as inst:
            logger.error(f"EXCEPTION: {inst}")
            logger.error(f"exec_info={sys.exc_info()}")
            pass

        if not em_id:
            return None

        if contact.last_contacted is None or contact.last_contacted < date_:
            contact.last_contacted = date_
            contact.save()

        try:
            # ???: Is there ever a situation where an EmailAccount
            #      wouldn't have a user or userprofile?
            up = self.user.userprofile
        except:
            up = None

        if up:
            name = 'received_email' if em.inbox else 'emailed'
            up.add_event(name=name, contact=em.contact, start=em.sent_date, created=em.sent_date)
            up.add_contact_rep(em.contact)

        em = EmailMsg.objects.filter(id=em_id).first()
        if em is None:
            logger.error(f"Unable to reload EmailMsg.id={self.id}: {sys.exc_info()}")
            return None

        # If the email was saved successfully, do post-processing on the EmailMsg
        # NOTE: The process_msg functions and it's variations are static methods.
        if type == 'imap' or type == 'gmailApi':
            EmailMsg.process_msg(em, email_msg, self, contact)
        elif type == 'office':
            EmailMsg.process_office_msg(em, email_msg, self, contact, message_id,
                                        ext_dtl['has_attachments'],
                                        ext_dtl['access_token'],
                                        ext_dtl['user_email'])
        elif type == 'api':
            EmailMsg.process_api_msg(em, email_msg, self, contact, ext_dtl['has_attachments'])
        return em

    ############################################################################
    # Purpose: Manually parses a MIME message, extracting various parts of it
    #   and passing them into the save_message function
    #
    #   :param email_msg: email parser object
    #   :param msg_id: server-side message id.
    # NOTE: This is NOT the message-id from inside the email.
    #       It is used as a secondary identifier to uniquely identify the email in the database.
    ############################################################################
    def process_mime_message(self, email_msg, msg_id):
        ep = re.compile('<(.*)>')
        message_id = None

        # Extract the message-id field from the email
        if 'message-id' in email_msg:
            message_id = email_msg['message-id'].strip()[:255]
        else:
            # Create a UTF-8 encoded string that concatenates the msg_id and username fields
            # Then create an MD5 hash of that string to use as the message_id
            temp_message_id = ("%s%s" % (str(msg_id or ''), self.username)).encode('utf-8')
            message_id = hashlib.md5(temp_message_id).hexdigest()

        # find the Email in the database by its message-id
        em = EmailMsg.objects.filter(company=self.company,
                                     user=self.user,
                                     message_id=message_id).first()

        # If we already have this email in the database, we can skip it and move on to the next one
        if em:
            try:
                maillog('Got this email already: %s' % message_id)
            except:
                logger.error('Fetch Mail Cron Job Error Acc ID: %s', self.id,
                             exc_info=sys.exc_info())
            return

        # extract the subject of the email
        try:
            subject = email_msg['subject'][:255]
        except:
            subject = ''

        # extract the date of the email
        try:
            date_ = parse(email_msg['date'])
        except:
            date_ = None
            try:
                date_ = email.utils.parsedate_to_datetime(email_msg['date'])
            except:
                # logger.error(f"Failed email.utils.parsedate_to_datetime({email_msg['date']})")
                return

        # These appear intended to initially gather the fields from the email
        # because they're effectively stored as a CSV list.
        # Once the data from the field is obtained, the code iterates over the values
        # of the CSV list, stripping out everything except for the email addresses themselves.
        from_ = None
        tos_, tos__ = [], []
        cc_, cc__ = [], []
        bcc_, bcc__ = [], []
        all_recipients_ = []

        # Parse 'From'
        try:
            email_msg_from = email_msg['from']
        except:
            email_msg_from = None

        # parse the from field
        if email_msg_from:
            if email_msg_from.find('<') > -1:
                try:
                    from_ = ep.search(email_msg_from).group(1)[:80].strip().lower()
                except:
                    from_ = None
            else:
                from_ = email_msg_from[:80].strip().lower()

        # if the from field isn't set, then exit this function
        if from_ is None or len(from_) == 0:
            # logger.error("From email address not found")
            return

        # Extract the 'to' field
        try:
            email_msg_to = email_msg['to'].strip().lower()
        except:
            email_msg_to = None

        # Now create an array of those "to" email addresses
        if email_msg_to:
            if email_msg_to.find(',') > -1:
                tos__ = email_msg_to.strip().lower().split(',')
            else:
                tos__ = [email_msg_to.strip().lower()]

        # iterate over the list of 'to' values, and get
        for t in tos__:
            if t.find('<') > -1:
                try:
                    # parse the email address itself
                    to_ = ep.search(t).group(1)[:80].strip().lower()
                except:
                    to_ = None
            else:
                to_ = t[:80].strip().lower()

            # if the to_ field that we extracted above is valid, append it to the list
            if to_ and len(to_) != 0:
                tos_.append(to_)

        # verify the length of the resulting array of 'To' email addresses
        if len(tos_) == 0:
            try:
                maillog('To email ids not found')
            except:
                logger.error('Fetch Mail Cron Job Error Acc ID: %s', self.id, exc_info=sys.exc_info())
            return

        # Parse 'CC'
        try:
            email_msg_cc = email_msg['cc'].strip().lower()
        except:
            email_msg_cc = None

        # if email_msg_cc contained data, create a list, split by commas
        if email_msg_cc:
            if email_msg_cc.find(',') > -1:
                cc__ = email_msg_cc.strip().lower().split(',')
            else:
                cc__ = [email_msg_cc.strip().lower()]

        # now parse the cc__ list to get just the email addresses
        for t in cc__:
            if t.find('<') > -1:
                try:
                    # parse the email address itself
                    to_cc_ = ep.search(t).group(1)[:80].strip().lower()
                except:
                    to_cc_ = None
            else:
                to_cc_ = t[:80].strip().lower()

            if to_cc_ and len(to_cc_) != 0:
                cc_.append(to_cc_)

        # Parse 'BCC'
        try:
            email_msg_bcc = email_msg['bcc'].strip().lower()
        except:
            email_msg_bcc = None

        # create a list from the CSV list of email addresses
        if email_msg_bcc:
            if email_msg_bcc.find(',') > -1:
                bcc__ = email_msg_bcc.strip().lower().split(',')
            else:
                bcc__ = [email_msg_bcc.strip().lower()]

        # iterate over these values, creating a list of only the email addresses
        for t in bcc__:
            if t.find('<') > -1:
                try:
                    # parse the email address itself
                    to_bcc_ = ep.search(t).group(1)[:80].strip().lower()
                except:
                    to_bcc_ = None
            else:
                to_bcc_ = t[:80].strip().lower()

            if to_bcc_ and len(to_bcc_) != 0:
                bcc_.append(to_bcc_)

        # Aggregate all of the recipients into a single list
        try:
            all_recipients_ = tos_ + cc_ + bcc_
        except:
            logger.error('Fetch Mail Cron Job Error Acc ID: %s', self.id, exc_info=sys.exc_info())

        # verify that there are one or more recipients
        if len(all_recipients_) == 0:
            logger.debug("No recipients")
            return

        # Now that we've passed all of the validation and parsing, save this message
        # self.save_message(from_, tos_, subject, email_msg, message_id, date_, [], 'imap')
        self.save_message(from_, all_recipients_, subject, email_msg, message_id, date_, [], 'imap')

    def process_gmail_messages(self, service, messages):
        for message in messages:
            msg_id = message['id']
            email_msg = em.oauth2.get_mime_message(service, msg_id)
            self.process_mime_message(email_msg, msg_id)

    def sync_gmail_emails(self, long_check, days):
        try:
            credentials = em.oauth2.exchange_access_token(self.oauth_refresh_token)
            service = build('gmail', 'v1', credentials=credentials)

            # Identify the target ImapFolders we want to synchronize locally
            imap_folders = ImapFolder.objects.filter(company=self.company,
                                                     user=self.user,
                                                     account=self,
                                                     check=True)

            # If this is a long_check, exclude those where the long_check has been done
            if long_check:
                imap_folders = imap_folders.exclude(long_check_done=True)

            # Retrieve the label names for each of the ImapFolders and add them into an array
            label_ids = [str(imp.name) for imp in imap_folders]

            # Loop through the labes and retrieve the messages
            for label_id in label_ids:
                maillog("******************* {} **************".format(label_id))
                response = em.oauth2.get_messages(service, days, label_id)

                # Assuming the previous request doesn't throw an error,
                # this will reset the failed_count
                self.password_success()
                if 'messages' in response:
                    self.process_gmail_messages(service, response['messages'])
                if 'nextPageToken' in response:
                    while 'nextPageToken' in response:
                        page_token = response['nextPageToken']
                        response = em.oauth2.get_messages(service, days, label_id, page_token)
                        if 'messages' in response:
                            self.process_gmail_messages(service, response['messages'])
        except Exception as e:
            if 'invalid_grant' in str(e):
                logger.error("invalid_grant detected")
                self.password_fail()
            logger.error('Fetch GMail Cron Job Error Acc ID: %s', self.id, exc_info=sys.exc_info())

    def sync_office_emails(self, long_check, days):
        response = officeservice.get_token_from_refresh_token(self.oauth_refresh_token,
                                                              settings.OFFICE_REDIRECT_URI)
        try:
            if response['access_token']:
                try:
                    self.oauth_refresh_token = response['refresh_token']
                    self.save()
                except:
                    pass
                imfs = ImapFolder.objects.filter(company=self.company,
                                                 user=self.user,
                                                 account=self,
                                                 check=True)

                if long_check:
                    imfs = imfs.exclude(long_check_done=True)
                for imf in imfs:
                    folder_id = imf.name
                    maillog("imf name %s" % imf.pretty_name)
                    for since_x in range(days, -1, -1):
                        since = timezone.localtime(timezone.now()) - timedelta(days=since_x)
                        before = since + timedelta(days=1)
                        since_before = '(SINCE "%s" BEFORE "%s")' % (
                            since.strftime('%Y-%m-%d'), before.strftime('%Y-%m-%d'))
                        maillog('since_before: %s' % since_before)

                        start_date = since.strftime('%Y-%m-%d')
                        end_date = before.strftime('%Y-%m-%d')
                        messages = officeservice.get_messages(response['access_token'],
                                                              self.username,
                                                              folder_id,
                                                              start_date,
                                                              end_date)
                        try:
                            try:
                                messages = messages['value']
                            except:
                                messages = []
                            for message in messages:
                                emsl = None
                                message_id = message['id'].strip()[:255]

                                try:
                                    from_ = message['from']['emailAddress']['address'].lower()
                                except:
                                    try:
                                        from_ = message['sender']['emailAddress']['address'].lower()
                                    except:
                                        continue

                                tos_ = []
                                subject = message['subject']
                                email_msg = message['body']
                                receivedDateTime = parse(message['receivedDateTime'])
                                for recipients in message['toRecipients']:
                                    try:
                                        tos_.append(recipients['emailAddress']['address'].lower())
                                        continue
                                    except:
                                        ens = recipients['emailAddress']['name'].lower()
                                        tos_.extend(list(map(str.strip, ens.split(';'))))
                                ext_dtl = {
                                    'access_token': response['access_token'],
                                    'user_email': self.address,
                                    'has_attachments': message['hasAttachments']
                                }
                                try:
                                    em = EmailMsg.objects.filter(company=self.company,
                                                                 user=self.user,
                                                                 message_id=message_id)[:1][0]
                                    maillog('Got this email already: %s' % message_id)
                                except:
                                    self.save_message(from_, tos_, subject,
                                                      email_msg, message_id, receivedDateTime,
                                                      ext_dtl, 'office')
                        except Exception as e:
                            logger.error('Fetch Mail Cron Job Error Office Acc ID: %s, exc: %s, folder:%s, msg: %s',
                                         self.id, e, imf.id, messages,
                                         exc_info=sys.exc_info())
                            continue
                if self.passwd_failing:
                    self.passwd_failing = False
                    self.failed_count = 0
                    self.save()
        except Exception as e:
            logger.error('Fetch Mail Cron Job Error Acc ID: %s,exc: %s',
                         self.id, e,
                         exc_info=sys.exc_info())
            self.password_fail()
            return False

    def check_imap4(self, long_check=False, since=None):
        # Skip this email account if the company is disabled
        if self.company.disabled:
            return

        # Skip this email account if the company account is configured to not use email sync
        if not self.company.check_email:
            return

        # Skip syncing email accounts where the password is failing and has failed
        #   more than the target maximum
        if self.passwd_failing and self.failed_count > EmailAccount.max_failed_count():
            return

        # Skip syncing email accounts which are disabled or deleted
        if self.disabled or self.deleted:
            return

        # If this is a long_check, then use the target number of days.
        #   Otherwise, default to 1 day.
        days_to_sync = self.company.imap_long_check_days if long_check else 1

        # If a target date was provided, it should override the defaults.
        #   In that case, we will use the date provded to calculate the days_to_sync
        if since:
            since = parse(since)
            days_to_sync = (timezone.localtime(timezone.now()) - since).days

        # Prevent the days_to_sync from exceeding the global maximum
        if days_to_sync > settings.IMAP_LONG_CHECK_DAYS:
            days_to_sync = settings.IMAP_LONG_CHECK_DAYS

        # Prevent the days_to_sync from being less than 1
        if days_to_sync < 1:
            days_to_sync = 1

        maillog('\n**** Checking IMAP4 %s ****' % timezone.localtime(timezone.now()))
        maillog('address: %s' % self.address)
        maillog('hostname: %s' % self.hostname)
        maillog('username: %s' % self.username)
        maillog('long_check: %s' % long_check)
        maillog('days_to_sync: %s' % days_to_sync)

        if not long_check:
            # if this is a regular sync, don't do it again if the account was synced
            #   within the last 10 minutes. This plays nice with mail servers and
            #   aligns with Google's requests to sync no more than every 10 minutes.
            ten_minutes_ago = (timezone.localtime(timezone.now()) - timedelta(minutes=10))
            if self.last_checked and self.last_checked > ten_minutes_ago:
                maillog('email sync attempted too soon')
                # return

        # BUG: The connection hasn't been verified, so setting this flag means that
        #   attempts to connect that fail cannot be retried within the next 10 minutes.
        #   This logic is faulty
        self.last_checked = timezone.localtime(timezone.now())
        self.save()

        if self.is_using_office365_oauth():
            maillog("is_using_office365_oauth() == True")
            return self.sync_office_emails(long_check, days_to_sync)
        elif self.is_using_google_oauth():
            maillog("is_using_google_oauth() == True")
            return self.sync_gmail_emails(long_check, days_to_sync)

        imap_mailbox = self.make_login()
        maillog("after imap_mailbox connection established")
        maillog('imap_mailbox: %s' % imap_mailbox)
        if not imap_mailbox:
            return False

        maillog("before imap_folders query")
        imap_folders = ImapFolder.objects.filter(company=self.company,
                                                 user=self.user,
                                                 account=self,
                                                 check=True)
        maillog('imap_folders: %s' % imap_folders)
        if long_check:
            imap_folders = imap_folders.exclude(long_check_done=True)
            maillog('imap_folders: %s' % imap_folders)

        imap_folders = imap_folders.order_by('id')
        num = None

        for imap_folder in imap_folders:
            maillog('imap_folder: %s' % imap_folder.name)

            # This looks like a bug because it marks the folder as having completed
            #   a long_check before it actually completes. If there are any errors,
            #   then this flag will be wrong.
            if long_check:
                imap_folder.long_check_done = True
                maillog('imap_folder.long_check_done: %s' % imap_folder.name)

                try:
                    imap_folder.save()
                    maillog("********* ImapFolder.long_check_done Saved")
                except:
                    pass

            try:
                s = imap_mailbox.select('"%s"' % imap_folder.name, readonly=True)
                try:
                    if s[0] == 'OK':
                        num = s[1][0].decode('utf-8')
                    else:
                        pass
                except:
                    pass
            except ssl.SSLError:
                pass
            except:
                maillog("********* RE establishing the connection")
                imap_mailbox = self.make_login()
                if not imap_mailbox:
                    return False
                try:
                    s = imap_mailbox.select('"%s"' % imap_folder.name, readonly=True)
                    try:
                        if s[0] == 'OK':
                            num = s[1][0].decode('utf-8')
                        else:
                            pass
                    except:
                        pass
                except:
                    continue

            # AIT - The below changes were made to pull out first 1,000 emails of the mailbox
            #   as a hotfix for the mailboxes connected using the IMAP4 protocol.
            if num:
                for since_x in range(int(num), int(num) - 1000, -1):
                    try:
                        search_resp, search_data = imap_mailbox.search(None, "ALL")
                    except:
                        search_rep, search_data = None, None

                    try:
                        msg_ids = search_data[0].split()
                    except:
                        msg_ids = []

                    emsl = None
                    try:
                        fetch_resp, fetch_data = imap_mailbox.fetch(str(since_x), '(RFC822)')
                    except:
                        continue

                    try:
                        email_msg = fetch_data[0][1]
                    except:
                        email_msg = None

                    if email_msg and isinstance(email_msg, str):
                        try:
                            email_msg = email.message_from_string(email_msg)
                        except:
                            email_msg = None
                    elif email_msg and isinstance(email_msg, bytes):
                        try:
                            email_msg = email.message_from_bytes(email_msg)
                        except:
                            email_msg = None

                    if email_msg:
                        self.process_mime_message(email_msg, since_x)

        try:
            imap_mailbox.close()
        except:
            pass

        try:
            imap_mailbox.logout()
        except:
            pass
        maillog('**** Done Checking IMAP4 ****')

    def find_imported_message_identifiers_by_message_id(self, message_id):
        """
        Search for an EmailMsg with the specified message-id
        @param message_id: string, representing the Message-Id from the email
        @return: dictionary of the values from the target row,
                 or None
        """
        return EmailMsg.objects.filter(account=self, message_id=message_id)\
            .values('id',
                    'to_email',
                    'message_id',
                    'bucket_name',
                    'bucket_path')\
            .first()


class EmailMsg(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    account = models.ForeignKey(EmailAccount, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, null=True, on_delete=models.SET_NULL)
    content = models.TextField(max_length=16777216)  # 16MB
    text_plain = models.TextField(max_length=1048576, null=True, blank=True)  # 1MB
    text_html = models.TextField(max_length=1048576, null=True, blank=True)  # 1MB
    to_email = models.TextField()
    from_email = models.TextField(max_length=80)
    message_id = models.TextField(max_length=255)
    url_hash = models.TextField(max_length=80)
    subject = models.TextField(max_length=255)
    inbox = models.BooleanField(default=True)
    sent_date = models.DateTimeField()
    created = models.DateTimeField()
    bucket_name = models.CharField(max_length=64, null=True, blank=True)
    bucket_path = models.CharField(max_length=1024, null=True, blank=True)

    @staticmethod
    def decode_types():
        return [
            'application/ics',
            'application/ms-tnef',
            'application/msword',
            'application/octet-stream',
            'application/pdf',
            'application/vnd.ms-excel',
            'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
            'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
            'audio/x-wav',
            'image/bmp',
            'image/gif',
            'image/jpg',
            'image/jpeg',
            'image/png',
            'image/svg+xml',
            'image/tiff',
            'text/calendar',
            'text/csv',
            'text/directory',
            'text/enriched',
            'text/x-vcard',
            'video/quicktime',
        ]

    # Given a list of email addresses, return a list of unique email addresses
    # that appear in the original list using all lowercase letters.
    @staticmethod
    def parse_unique_recipients(data):
        # declare a dictionary to identify email addresses in the original list
        # which have already been seen, and a list to house the results of
        # the search for unique, lowercase email addresses.
        seen, result = set(), []
        for item in data:
            if item.lower() not in seen:
                seen.add(item.lower())
                result.append(item.lower())
        return result

    @staticmethod
    def save_file(name, data):
        if name is None:
            return

        now = timezone.localtime(timezone.now())

        f_parts = name.split('.')
        e = f_parts[len(f_parts) - 1]

        s = '%s%s' % (now, name)
        h = hashlib.sha1(str(s).encode('utf-8')).hexdigest()

        d = '%s/%s/%s/%s/%s' % (settings.USER_FILES, h[0:2], h[2:4], h[4:6], h[6:8])

        try:
            os.makedirs(d)
        except:
            pass

        try:
            os.chmod(d, 0o777)
        except:
            pass

        filepath = '%s.%s' % (h, e)

        p = '%s/%s' % (d, filepath)

        dest = open(p, 'wb+')
        dest.write(data)
        dest.close()

        try:
            os.chmod(p, 0o777)
        except:
            pass

        # chmod parent dirs
        d = '%s/%s/%s/%s' % (settings.USER_FILES, h[0:2], h[2:4], h[4:6])
        try:
            os.chmod(d, 0o777)
        except:
            pass

        d = '%s/%s/%s' % (settings.USER_FILES, h[0:2], h[2:4])
        try:
            os.chmod(d, 0o777)
        except:
            pass

        d = '%s/%s' % (settings.USER_FILES, h[0:2])
        try:
            os.chmod(d, 0o777)
        except:
            pass

        return filepath

    @staticmethod
    def replace_img_tags(files, html):
        if len(files) > 0:
            for f in files:
                print(f"\nf.id: {f.id}")
                print(f"f.filename: {f.filename}")
                ip = re.compile('(<img)(.*)src="cid:(%s)@.*"\ (.*>)' % f.filename.replace(")", "\)").replace("(", "\("))
                m = ip.search(html)

                if m is None:
                    ip = re.compile('(<img)(.*)src="cid:(%s)@.*"(>)' % f.filename.replace(")", "\)").replace("(", "\("))
                    m = ip.search(html)

                if m:
                    img_tag = '%s%ssrc="%s" %s' % (m.group(1), m.group(2), f.get_fileurl(), m.group(4))
                    html = html.replace(m.group(0), img_tag)

        return html

    @staticmethod
    def replace():
        # not regex
        return [['=\n', ''],
                ['=\r\n', ''],
                ['=\r', ''],
                ['=A0', '&nbsp;'],
                # [ '=C2',      '&#194;'  ],
                ['=C2', '&nbsp;'],
                ['=E2', '&#226;'],
                ['=09', '&#009;'],
                ['=20', ' '],
                ['=80', '&#128;'],
                ['=85', '&#133;'],
                ['=92', "'"],
                ['=99', '&#153;'],
                ['3D"', '"'],
                ['""', '"'],
                ['</body>', ''],
                ['</html>', ''],
                ]

    @staticmethod
    def replace_regex():
        return [['<script.*?>.*</script>', ''],
                ['<style.*?>.*</style>', ''],
                ['<head.*?>.*</head>', ''],
                ['<html.*?>', ''],
                ['<body.*?>', ''],
                ]

    @staticmethod
    def process_msg(em, email_msg, account, contact):
        # For multi-part messages, process each individual part of the message
        if email_msg.is_multipart():
            parts_count = len(email_msg.get_payload())
            for x in range(0, parts_count):
                EmailMsg.process_msg(em, email_msg.get_payload()[x], account, contact)
            return

        # based on the message encoding, retrieve the payload
        try:
            encoding = email_msg['content-transfer-encoding']
        except:
            encoding = None

        try:
            payload = email_msg.get_payload()
        except:
            payload = ''

        if encoding and encoding == 'base64':
            try:
                payload = base64.b64decode(payload).decode()
            except:
                payload = base64.b64decode(payload)

        if email_msg.get_content_type() == 'text/html':
            em.text_html = payload
            em.save()
            return

        if email_msg.get_content_type() == 'text/plain':
            em.text_plain = payload
            em.save()
            return

        if email_msg.get_content_type() in EmailMsg.decode_types():
            try:
                filename = email_msg.get_filename()
            except:
                filename = None

            if filename:
                p_decoded = email_msg.get_payload(decode=True)
                filepath = EmailMsg.save_file(filename, p_decoded)
                now = timezone.localtime(timezone.now())
                uf = UserFile(company=em.company,
                              user=em.user,
                              filename=filename,
                              filepath=filepath,
                              created=now,
                              updated=now)

                try:
                    uf.save()
                    uf_id = uf.id
                except:
                    uf_id = None

                if uf_id:
                    cuf = ContactUserFile(company=em.company,
                                          contact=contact,
                                          user_file=uf,
                                          email_msg=em,
                                          account=account)
                    cuf.save()
        else:
            maillog('add to decode_types: {}'.format(email_msg.get_content_type()))
            return

    @staticmethod
    def process_office_msg(em, body, account, contact, message_id,
                           has_attachments, access_token, user_email):
        content_type = body['contentType']
        payload = body['content']
        now = timezone.localtime(timezone.now())
        if content_type == 'html':
            em.text_html = payload
            em.save()

        elif content_type == 'text/plain':
            em.text_plain = payload
            em.save()

        if not has_attachments:
            return

        try:
            attachments = officeservice.get_my_attachment(access_token, user_email, message_id)
            for attachment in attachments['value']:
                filename = attachment['name']
                p_decoded = base64.b64decode(attachment['contentBytes'])
                filepath = EmailMsg.save_file(filename, p_decoded)
                uf = UserFile(company=em.company,
                              user=em.user,
                              filename=filename,
                              filepath=filepath,
                              created=now,
                              updated=now)
                try:
                    uf.save()
                    uf_id = uf.id
                except:
                    uf_id = None

                if uf_id:
                    cuf = ContactUserFile(company=em.company,
                                          contact=contact,
                                          user_file=uf,
                                          email_msg=em,
                                          account=account)
                    cuf.save()
        except:
            pass

    @staticmethod
    def process_api_msg(em, body, account, contact, has_attachments):
        content_type = body['content_type']
        payload = body['content']
        now = timezone.localtime(timezone.now())
        if content_type == 'html':
            em.text_html = payload
            em.save()
        elif content_type == 'text/plain':
            em.text_plain = payload
            em.save()

        if not has_attachments:
            return

        try:
            attachments = body['attachments']
            for attachment in attachments:
                filename = attachment['name']
                p_decoded = base64.b64decode(attachment['file_data'])
                filepath = EmailMsg.save_file(filename, p_decoded)
                uf = UserFile(company=em.company,
                              user=em.user,
                              filename=filename,
                              filepath=filepath,
                              created=now,
                              updated=now)
                try:
                    uf.save()
                    uf_id = uf.id
                except:
                    uf_id = None

                if uf_id:
                    cuf = ContactUserFile(company=em.company,
                                          contact=contact,
                                          user_file=uf,
                                          email_msg=em,
                                          account=account)
                    cuf.save()
        except:
            pass

    def next_msg(self):
        em = EmailMsg.objects \
            .filter(company=self.company,
                    user=self.user,
                    inbox=self.inbox,
                    sent_date__lt=self.sent_date) \
            .order_by('-sent_date') \
            .first()
        return em

    def prev_msg(self):
        em = EmailMsg.objects \
            .filter(company=self.company,
                    user=self.user,
                    inbox=self.inbox,
                    sent_date__gt=self.sent_date) \
            .order_by('sent_date').first()
        return em

    def has_plain(self):
        return True if self.text_plain and len(self.text_plain) > 0 else False

    def has_html(self):
        return True if self.text_html and len(self.text_html) > 0 else False

    def get_text_plain(self):
        t = self.text_plain
        if t is None:
            return ''
        rs = [['\n', '<br />'], ]
        for r in EmailMsg.replace():
            t = t.replace(r[0], r[1])
        for r in rs:
            t = t.replace(r[0], r[1])
        return t

    def get_text_html(self):
        h = self.text_html
        if h is None:
            return ''

        for r in EmailMsg.replace_regex():
            h = h.replace(r[0], r[1])

        for r in EmailMsg.replace():
            h = h.replace(r[0], r[1])

        files = self.get_files()

        # 'cause there maybe same-named images used multiple times
        for x in range(0, 10):
            h = EmailMsg.replace_img_tags(files, h)

        return h

    def has_files(self):
        cuf = ContactUserFile.objects.filter(company=self.company, email_msg=self).first()
        return True if cuf else False

    def get_files(self):
        files = []
        for cuf in ContactUserFile.objects.filter(company=self.company, email_msg=self).order_by('id'):
            files.append(cuf.user_file)
        return files

    def get_subject(self):
        s = self.subject
        return s if s else 'subject not found'

    def to_hash(self):
        try:
            rep = self.user.userprofile.to_hash()
        except:
            rep = None
        try:
            send_date = timezone.localtime(self.sent_date, timezone.get_current_timezone())
            send_date = send_date.strftime('%Y-%m-%d %H:%M:%S')
        except:
            send_date = ''
        try:
            created = timezone.localtime(self.created, timezone.get_current_timezone())
            created = created.strftime('%Y-%m-%d %H:%M:%S')
        except:
            created = ''
        files = [uf.to_hash() for uf in self.get_files()]
        return {
            'email_message_id': self.id,
            'rep': rep,
            'contact': self.contact.fullname(),
            'contact_id': self.contact_id,
            'contact_company_name': self.contact.contact_company.name if self.contact.contact_company else '',
            'inbox': '1' if self.inbox else '0',
            'subject': self.get_subject(),
            'has_files': '1' if self.has_files() else '0',
            'files': files,
            'send_date': send_date,
            'created': created
        }

    def get_contact_name(self):
        c_name = ''
        if self.company.people_tab:
            if self.inbox:  # - contact name is in form email
                try:
                    cp = ContactPersonnel.objects.filter(email__iexact=self.from_email,
                                                         contact=self.contact)[0]
                    c_name += '<a href="/contacts/%s/personnels/%s/edit/">%s</a><br />' % (
                        self.contact.id, cp.id, cp.fullname())
                except:
                    pass
            else:  # - names of related contacts are in to_email field
                try:
                    tos = EmailMsg.parse_unique_recipients(self.to_email.split('|'))
                    for to_ in tos:
                        for cp in ContactPersonnel.objects.filter(email__iexact=to_,
                                                                  contact=self.contact):
                            c_name += '<a href="/contacts/%s/personnels/%s/edit/">%s</a><br />' % (
                                self.contact.id, cp.id, cp.fullname())
                except:
                    pass
        else:
            c_name += '<a href="/contacts/edit/%s/">%s</a><br />' % \
                      (self.contact_id, self.contact.fullname())
        if self.contact.contact_company:
            c_name += '<a href="/contacts/edit/%s/">%s</a>' % \
                      (self.contact_id, self.contact.contact_company.name)
        return c_name


class UserFile(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    filename = models.CharField(max_length=255)
    filepath = models.CharField(max_length=80)
    created = models.DateTimeField()
    updated = models.DateTimeField()

    def get_contact(self):
        cuf = ContactUserFile.objects.filter(company=self.company, user_file=self).first()
        if cuf:
            return cuf.contact
        return None

    def get_mimetype(self):
        return 'application/x-download'

    def get_fileext(self):
        parts = self.filepath.split('.')
        if len(parts) > 0:
            return parts[len(parts) - 1]
        return ''

    def get_filepath(self):
        h = self.filepath
        d = '%s/%s/%s/%s/%s' % (settings.USER_FILES, h[0:2], h[2:4], h[4:6], h[6:8])
        return '%s/%s' % (d, h)

    def get_fileurl(self):
        h = self.filepath
        d = '%s/%s/%s/%s/%s' % (settings.USER_FILES_URL, h[0:2], h[2:4], h[4:6], h[6:8])
        return '%s/%s' % (d, h)

    def get_updated(self):
        return self.updated.strftime('%Y-%m-%d %H:%M')

    def is_shared(self):
        suf = SharedUserFile.objects.filter(company=self.company, user_file=self).first()
        return suf

    def shared_list(self):
        users = []
        for suf in SharedUserFile.objects.filter(company=self.company, user_file=self):
            users.append(suf.shared_user)
        users.sort(key=lambda user: user.first_name)
        return users

    def to_hash(self):
        share_reps = []
        for suf in SharedUserFile.objects.filter(company=self.company, user_file=self):
            try:
                share_reps.append(suf.shared_user.userprofile.to_hash())
            except:
                pass
        try:
            rep = self.user.userprofile.to_hash()
        except:
            rep = None
        try:
            created = timezone.localtime(self.created, timezone.get_current_timezone())
            created = created.strftime('%Y-%m-%d %H:%M:%S')
        except:
            created = ''
        try:
            updated = timezone.localtime(self.updated, timezone.get_current_timezone())
            updated = updated.strftime('%Y-%m-%d %H:%M:%S')
        except:
            updated = ''

        return {
            'user_file_id': self.id,
            'name': self.filename,
            'rep': rep,
            'url': self.get_fileurl(),
            'is_shared': '1' if self.is_shared() else '0',
            'reps': share_reps,
            'updated': updated,
            'created': created
        }


class ContactUserFile(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    user_file = models.ForeignKey(UserFile, on_delete=models.CASCADE)
    account = models.ForeignKey(EmailAccount, null=True, blank=True, on_delete=models.SET_NULL)
    email_msg = models.ForeignKey(EmailMsg, null=True, blank=True, on_delete=models.SET_NULL)


class SharedUserFile(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    shared_user = models.ForeignKey(User, on_delete=models.CASCADE)
    user_file = models.ForeignKey(UserFile, on_delete=models.CASCADE)


class ImapFolder(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    account = models.ForeignKey(EmailAccount, on_delete=models.CASCADE)
    name = models.TextField(max_length=255)  # Name of the folder (set to the folderId for Office365)
    pretty_name = models.TextField(max_length=255)  # Name of the folder (set to the displayName for Office365)
    check = models.BooleanField(default=False)  # Look in this folder when synchronizing?
    long_check_done = models.BooleanField(default=False)  # Has a historical sync been performed on this folder?
    created = models.DateTimeField()
    uid_validity = models.BigIntegerField(null=True)
    uid_next = models.BigIntegerField(null=True)
    message_count = models.IntegerField(null=True)
    last_seen = models.DateTimeField(null=True)
    last_sync_attempt_date = models.DateTimeField(null=True)
    last_sync_success_date = models.DateTimeField(null=True)


class BusinessCardDetails(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, null=True, blank=True, on_delete=models.SET_NULL)
    personnel = models.ForeignKey(ContactPersonnel, null=True, blank=True, on_delete=models.SET_NULL)
    image = ImageField(upload_to=business_card_image_path)
    business_card_back_image = ImageField(upload_to=business_card_image_path, null=True, blank=True)
    first_name = models.CharField(max_length=255, null=True, blank=True)
    last_name = models.CharField(max_length=255, null=True, blank=True)
    title = models.CharField(max_length=255, null=True, blank=True)
    company_name = models.CharField(max_length=255, null=True, blank=True)
    address = models.CharField(max_length=255, null=True, blank=True)
    website = models.CharField(max_length=255, null=True, blank=True)
    email = models.CharField(max_length=255, null=True, blank=True)
    phone_number = models.CharField(max_length=20, null=True, blank=True)
    notes = models.TextField(null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    is_deleted_from_scanner = models.BooleanField(default=False)


    def get_image_url(self):
        return self.image.url.replace(settings.MEDIA_ROOT, '')

    def get_back_image_url(self):
        return self.business_card_back_image.url.replace(settings.MEDIA_ROOT, '')


class ContactImage(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    cfield = models.ForeignKey(CField, null=True, blank=True, on_delete=models.SET_NULL)
    contact_event_form = models.ForeignKey(ContactEventForm,
                                           null=True,
                                           blank=True,
                                           on_delete=models.SET_NULL)
    business_card = models.ForeignKey(BusinessCardDetails, null=True, blank=True, on_delete=models.SET_NULL)
    image = ImageField(max_length=255, upload_to=contact_images_path)
    created = models.DateTimeField()

    def get_image_url(self):
        if not self.image:
            return None
        return self.image.url.replace(settings.MEDIA_ROOT, '')

    def to_hash(self):
        try:
            created = timezone.localtime(self.created, timezone.get_current_timezone())
            created = created.strftime('%Y-%m-%d %H:%M:%S')
        except:
            created = ''
        return {
            'via': self.contact_event_form.event_form.name if self.contact_event_form else '',
            'custom_field': self.cfield.name if not self.contact_event_form and self.cfield else '',
            'url': self.get_image_url(),
            'created': created
        }


class DeleteType(models.Model):
    name = models.CharField(max_length=32)

    def __str__(self):
        return '%s' % self.name.replace('_', ' ').title()


class DeleteAction(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    delete_type = models.ForeignKey(DeleteType, on_delete=models.CASCADE)
    created = models.DateTimeField()


class APIDataType(models.Model):
    name = models.CharField(max_length=32)


class APIEntity(models.Model):
    name = models.CharField(max_length=32)

    def pretty_name(self):
        n = self.name.replace('_', ' ').title()
        n = n.replace('Html', 'HTML')
        return n


class APIVerb(models.Model):
    name = models.CharField(max_length=32)


class APIKey(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    apidatatype = models.ForeignKey(APIDataType, on_delete=models.CASCADE)
    name = models.CharField(max_length=40)
    key = models.CharField(max_length=40)
    secret = models.CharField(max_length=40)
    active = models.BooleanField(default=True)

    def requests(self):
        count = 0
        api_req = APIRequest.objects.filter(company=self.company, apikey=self).first()
        if api_req:
            count = api_req.count

        return count

    def new_request(self):
        if not self.active:
            return

        api_req = APIRequest.objects.filter(company=self.company, apikey=self).first()
        if api_req:
            api_req.count += 1
        else:
            api_req = APIRequest(company=self.company, apikey=self)
        api_req.save()

    def save_usage(self, request):
        p = re.compile('[^-a-z\/_]')
        path = p.sub('', request.path).replace('//', '/').replace('//', '/')

        url = UsageURL.objects.filter(url=path).first()
        if url is None:
            url = UsageURL(url=path)
            try:
                url.save()
            except:
                pass

        if url and url.id:
            ur = UsageRequest(company=self.company,
                              user=self.user,
                              url=url,
                              created=timezone.localtime(timezone.now()))
            ur.save()


class APIAccess(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    apikey = models.ForeignKey(APIKey, on_delete=models.CASCADE)
    apientity = models.ForeignKey(APIEntity, on_delete=models.CASCADE)
    apiverb = models.ForeignKey(APIVerb, on_delete=models.CASCADE)


class APIRequest(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    apikey = models.ForeignKey(APIKey, on_delete=models.CASCADE)
    count = models.IntegerField(default=1)


class APIHistory(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    apikey = models.ForeignKey(APIKey, on_delete=models.CASCADE)
    apientity = models.ForeignKey(APIEntity, on_delete=models.CASCADE)
    apiverb = models.ForeignKey(APIVerb, on_delete=models.CASCADE)
    entity_id = models.IntegerField()
    created = models.DateTimeField()


class StatsHTML(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    html = models.CharField(max_length=4096, null=True, blank=True)

    def to_hash(self):
        try:
            user = self.user.userprofile.fullname()
        except:
            user = ''

        try:
            email = self.user.email
        except:
            email = ''

        data = {
            'user_id': self.user_id,
            'user': user,
            'email': email,
            'html': self.html,
        }

        return data


class SupportCategory(models.Model):
    name = models.CharField(max_length=64)
    position = models.IntegerField()


class UsageURL(models.Model):
    url = models.CharField(max_length=255, unique=True)

    def __str__(self):
        return '%s' % self.url


class UsageRequest(models.Model):
    company = models.ForeignKey(Company, null=True, blank=True, on_delete=models.SET_NULL)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    url = models.ForeignKey(UsageURL, on_delete=models.CASCADE)
    created = models.DateTimeField()

    def __str__(self):
        return '%s' % self.url


class UsageStat(models.Model):
    company = models.ForeignKey(Company, null=True, blank=True, on_delete=models.SET_NULL)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    url = models.ForeignKey(UsageURL, on_delete=models.CASCADE)
    date = models.DateField()
    count = models.IntegerField()


class EmailNonReg(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    email_id = models.CharField(max_length=64)
    email_type = models.ForeignKey(EmailType, on_delete=models.CASCADE)
    email_status = models.ForeignKey(EmailStatus, on_delete=models.CASCADE)
    hashed = models.CharField(max_length=40)
    subject = models.CharField(max_length=80)
    txt = models.TextField()
    html = models.TextField()
    opened = models.DateTimeField(null=True, blank=True)
    attempts = models.IntegerField()
    retry = models.DateTimeField(null=True, blank=True)
    updated = models.DateTimeField()
    created = models.DateTimeField()

    def pretty_date(self):
        return '%s' % self.created.strftime('%Y-%m-%d')


class Route(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    name = models.CharField(max_length=64)
    updated = models.DateTimeField()
    created = models.DateTimeField()

    def str_created(self):
        if self.created:
            self.created = timezone.localtime(self.created, timezone.get_current_timezone())
            return self.created.strftime('%Y-%m-%d %H:%M:%S')
        else:
            return ''


class RouteContact(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_ids = models.TextField(max_length=4096)
    user = models.ForeignKey(User, related_name='userKey',
                             null=True,
                             blank=True,
                             on_delete=models.SET_NULL)
    assigned_by = models.ForeignKey(User, null=True, blank=True, on_delete=models.SET_NULL)
    route = models.ForeignKey(Route, on_delete=models.CASCADE)
    updated = models.DateTimeField()
    created = models.DateTimeField()


class Youtubevideos(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    video_url = models.CharField(max_length=255)
    video_name = models.CharField(max_length=250)
    is_for_dashboard = models.BooleanField(default=False)
    startdate = models.DateTimeField()


class YoutubeVideoCount(models.Model):
    youtubevideo = models.ForeignKey(Youtubevideos, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    viewed_count = models.IntegerField()
    startdate = models.DateTimeField()


class LocationForm(ModelForm):
    class Meta:
        model = Location
        exclude = []


class WorkForm(ModelForm):
    class Meta:
        model = Work
        exclude = []


class CategoryForm(ModelForm):
    class Meta:
        model = Category
        exclude = []


class ContactPhoneForm(ModelForm):
    def __init__(self, *args, **kwargs):
        super(ContactPhoneForm, self).__init__(*args, **kwargs)
        self.fields['phone_type'].queryset = PhoneType.objects.order_by('position')

    class Meta:
        model = ContactPhone
        phone_number = CharField(required=True)
        country_code = CharField(required=True)
        exclude = ('contact', 'created', 'contact_type', 'dealer_store', 'forward_incoming_to')


class ContactNoteForm(ModelForm):
    class Meta:
        model = ContactNote
        note = CharField(required=True)
        exclude = []


class ContactTypeForm(ModelForm):
    class Meta:
        model = ContactType
        name = CharField(required=True)
        exclude = []


class ContactInfoEmailForm(ModelForm):
    class Meta:
        model = ContactInfoEmail
        email = EmailField(required=True)
        exclude = ('contact', 'created')


class ContactForm(ModelForm):
    def __init__(self, company, contact_company, *args, **kwargs):
        super(ContactForm, self).__init__(*args, **kwargs)
        self.fields['state'].queryset = State.objects.order_by('name')
        self.fields['contact_type'].queryset = ContactType.objects\
            .filter(company=company).order_by('name')
        self.fields['contact_company'].queryset = ContactCompany.objects\
            .filter(company=company).order_by('name')
        country = Country.objects.filter(name='United States').first()
        if country:
            self.fields['country'].initial = country

        if contact_company:
            self.fields['contact_company'].initial = contact_company

    class Meta:
        model = Contact
        exclude = ('company', 'created_by', 'created')


class CallTypeForm(ModelForm):
    class Meta:
        model = CallType
        exclude = []


class CallForm(ModelForm):
    class Meta:
        model = Call
        exclude = []


class CountryForm(ModelForm):
    class Meta:
        model = Country
        name = CharField(required=True)
        exclude = []


class StateForm(ModelForm):
    class Meta:
        model = State
        name = CharField(required=True)
        abbr = CharField(required=True)
        exclude = []


class CompanyForm(ModelForm):
    class Meta:
        model = Company
        name = CharField(required=True)
        exclude = []


class ContactCompanyForm(ModelForm):
    class Meta:
        model = ContactCompany
        name = CharField(required=True)
        exclude = []

    def __init__(self, company, contact_company, *args, **kwargs):
        super(ContactCompanyForm, self).__init__(*args, **kwargs)
        self.fields['primary_contact'].queryset = \
            Contact.objects.filter(company=company,
                                   contact_company=contact_company)\
                .order_by('first_name')


class UserForm(ModelForm):
    class Meta:
        model = User
        exclude = ('date_joined', 'last_login')

    email = EmailField()
    username = UsernameField(max_length=30, required=True)
    password = CharField(required=True)
    password2 = CharField(required=True)
    first_name = CharField(required=True)
    last_name = CharField(required=True)

    def check_password(self):
        if self.data['password'] != self.data['password2']:
            raise ValidationError('Passwords must match')
        return self.data['password']

    def clean(self, *args, **kwargs):
        self.check_password()
        return super(UserForm, self).clean(*args, **kwargs)


class UserProfileForm(ModelForm):
    class Meta:
        model = UserProfile
        exclude = ["task_notification_time",
                   "is_show_task_popup",
                   "google_cal_sync",
                   "task_popup_disabled",
                   "mobile_last_login",
                   "cal_followup",
                   "office_cal_followup",
                   "hide_mobile_appt_popup",
                   "call_review_automation_permission",
                   "can_make_store_announcement",
                   "can_add_custom_links"
                   ]

    def __init__(self, company, *args, **kwargs):
        super(UserProfileForm, self).__init__(*args, **kwargs)
        self.fields['store'].queryset = DealerStore.objects.filter(company=company).order_by('name')
        self.fields['title'].queryset = Title.objects.filter(company=company).order_by('name')
        self.fields['state'].queryset = State.objects.order_by('id')
        self.fields['places_cat_list'].queryset = PlacesCategoryList.objects.filter(
            Q(company=company) | Q(company=None)
        ).order_by('id')


class UserPhoneForm(ModelForm):
    def __init__(self, *args, **kwargs):
        super(UserPhoneForm, self).__init__(*args, **kwargs)
        self.fields['phone_type'].queryset = PhoneType.objects.order_by('position')

    class Meta:
        model = UserPhone
        phone_number = CharField(required=True)
        country_code = CharField(required=True)
        exclude = ('user', 'created')


class PhoneTypeForm(ModelForm):
    class Meta:
        model = PhoneType
        name = CharField(required=True)
        exclude = []


class PointForm(ModelForm):
    class Meta:
        model = Point
        exclude = []


class EventTypeForm(ModelForm):
    class Meta:
        model = EventType
        exclude = []


class EventTypePointForm(ModelForm):
    class Meta:
        model = EventTypePoint
        exclude = []


class UploadFileForm(Form):
    file = FileField()


class UserMarket(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    market = models.ForeignKey(Market, null=True, blank=True, on_delete=models.SET_NULL)


class TwilioCountry(models.Model):
    name = models.CharField(max_length=200)
    iso_code = models.CharField(max_length=3)
    code = models.CharField(max_length=5)
    created = models.DateTimeField()
    deleted = models.BooleanField(default=False)


class CompanyUserPrice(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    users = models.IntegerField()
    price = models.DecimalField(max_digits=11, decimal_places=2)


class TwilioCarrier(models.Model):
    name = models.CharField(max_length=255)
    shortname = models.CharField(max_length=255)
    created = models.DateTimeField()


class ContactMenuType(models.Model):
    name = models.CharField(max_length=20)


class ContactMenu(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=65)
    type = models.ForeignKey(ContactMenuType, on_delete=models.CASCADE)
    position = models.SmallIntegerField()
    is_hide = models.BooleanField(default=False)
    event_form = models.ForeignKey(EventForm, null=True, blank=True, on_delete=models.CASCADE)
    location = models.TextField()
    contactmenulist = models.ForeignKey('ContactMenuList',
                                        null=True,
                                        blank=True,
                                        on_delete=models.CASCADE)

    def to_hash(self, contact=None):
        title = self.name
        is_valid = 1  # - valid event form menu
        error_message = ''
        treat_as = 0
        account_id = "0"
        try:
            if self.location.find("omegaedi.com") > 1:
                self.type.id = 24
                if contact:
                    account_id = contact.account
            title = self.event_form.name
            treat_as = self.event_form.event_form_treat_as_id if self.event_form.event_form_treat_as_id else 0
            if contact:
                account_id = contact.account
                efct = EventFormContactType.objects.filter(event_form=self.event_form).first()
                if efct is not None:
                    try:
                        EventFormContactType.objects.filter(event_form=self.event_form,
                                                            contact_type=contact.contact_type)[:1][0]
                    except:
                        is_valid = 0  # - not a valid event form menu
                        error_message = "This is an Event Form that cannot be used for this type of contact. The form you requested is limited to specific contact types. Please check with your administrator or your CallProof Customer Experience Professional regarding the specific details."
        except:
            pass
        return {
            "Title": title,
            "regular_id": self.type.id,
            "event_form_id": self.event_form_id,
            "treat_as": treat_as,
            "redirection_url": self.location,
            "error_message": error_message,
            "is_valid": is_valid,
            "account_id": account_id

        }


class AppointmentPersonnel(models.Model):
    appointment = models.ForeignKey(Appointment, on_delete=models.CASCADE)
    personnel = models.ForeignKey(ContactPersonnel, on_delete=models.CASCADE)

    def fullname(self):
        return '%s %s' % (self.personnel.first_name, self.personnel.last_name)


class FollowupPersonnel(models.Model):
    followup = models.ForeignKey(Followup, on_delete=models.CASCADE)
    personnel = models.ForeignKey(ContactPersonnel, on_delete=models.CASCADE)

    def fullname(self):
        return '%s %s' % (self.personnel.first_name, self.personnel.last_name)


class ContactEventFormPersonnel(models.Model):
    contacteventform = models.ForeignKey(ContactEventForm, on_delete=models.CASCADE)
    personnel = models.ForeignKey(ContactPersonnel, on_delete=models.CASCADE)


class PeopleRun(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    status = models.CharField(max_length=15)  # pending, progress, completed
    created = models.DateTimeField()
    updated = models.DateTimeField()


class MergePeopleDuplicates(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    status = models.CharField(max_length=15)  # pending, progress, completed
    created = models.DateTimeField()
    updated = models.DateTimeField()


class UserBeacons(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    beacon = models.ForeignKey(Beacon, on_delete=models.CASCADE)
    created = models.DateTimeField()


class SmsTemplate(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    title = models.CharField(max_length=64, default='')
    template = models.TextField()
    created = models.DateTimeField(auto_now_add=True)
    updated = models.DateTimeField(auto_now=True)


class ContactResearch(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    store = models.ForeignKey(DealerStore, null=True, on_delete=models.SET_NULL)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, on_delete=models.CASCADE)
    first_name = models.CharField(max_length=50, null=True, blank=True)
    last_name = models.CharField(max_length=50, null=True, blank=True)
    email = models.CharField(max_length=50, null=True, blank=True)
    phone_number = models.CharField(max_length=15, null=True, blank=True)
    eligible = models.DateField(null=True, blank=True)
    phone_number1 = models.CharField(max_length=15, null=True, blank=True)
    eligible1 = models.DateField(null=True, blank=True)
    phone_number2 = models.CharField(max_length=15, null=True, blank=True)
    eligible2 = models.DateField(null=True, blank=True)
    phone_number3 = models.CharField(max_length=15, null=True, blank=True)
    eligible3 = models.DateField(null=True, blank=True)
    phone_number4 = models.CharField(max_length=15, null=True, blank=True)
    eligible4 = models.DateField(null=True, blank=True)
    phone_number5 = models.CharField(max_length=15, null=True, blank=True)
    eligible5 = models.DateField(null=True, blank=True)
    phone_number6 = models.CharField(max_length=15, null=True, blank=True)
    eligible6 = models.DateField(null=True, blank=True)
    phone_number7 = models.CharField(max_length=15, null=True, blank=True)
    eligible7 = models.DateField(null=True, blank=True)
    phone_number8 = models.CharField(max_length=15, null=True, blank=True)
    eligible8 = models.DateField(null=True, blank=True)
    phone_number9 = models.CharField(max_length=15, null=True, blank=True)
    eligible9 = models.DateField(null=True, blank=True)
    phone_number10 = models.CharField(max_length=15, null=True, blank=True)
    eligible10 = models.DateField(null=True, blank=True)
    created = models.DateTimeField()


class PeopleRole(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=64)


class ContactPhonePersonnel(models.Model):
    contactphone = models.ForeignKey(ContactPhone, on_delete=models.CASCADE)
    personnel = models.ForeignKey(ContactPersonnel, on_delete=models.CASCADE)
    extension = models.CharField(max_length=6, null=True, blank=True)

class Links(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name1 = models.CharField(max_length=250, null=True, blank=True)
    name2 = models.CharField(max_length=250, null=True, blank=True)
    name3 = models.CharField(max_length=250, null=True, blank=True)
    name4 = models.CharField(max_length=250, null=True, blank=True)
    name5 = models.CharField(max_length=250, null=True, blank=True)
    name6 = models.CharField(max_length=250, null=True, blank=True)
    link_url1 = models.TextField(null=True, blank=True)
    link_url2 = models.TextField(null=True, blank=True)
    link_url3 = models.TextField(null=True, blank=True)
    link_url4 = models.TextField(null=True, blank=True)
    link_url5 = models.TextField(null=True, blank=True)
    link_url6 = models.TextField(null=True, blank=True)
    created = models.DateTimeField()


class TwilioSipDomain(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    dealerstorephone = models.ForeignKey(DealerStorePhone, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    deleted_by = models.IntegerField()
    name = models.CharField(max_length=200, null=False, blank=False)
    domain_sid = models.CharField(max_length=48, null=False, blank=False)
    friendly_name = models.CharField(max_length=250, null=True, blank=True)
    is_deleted = models.BooleanField(default=False)
    created = models.DateTimeField()


class TwilioSipDomainCredentialList(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    deleted_by = models.IntegerField()
    credential_list_sid = models.CharField(max_length=48, null=False, blank=False)
    domain_list_sid = models.CharField(max_length=48, null=False, blank=False)
    friendly_name = models.CharField(max_length=250, null=True, blank=True)
    is_deleted = models.BooleanField(default=False)
    created = models.DateTimeField()


class TwilioSipCredential(models.Model):
    twiliosipdomaincredentiallist = models.ForeignKey(TwilioSipDomainCredentialList,
                                                      on_delete=models.CASCADE)
    credential_sid = models.CharField(max_length=48, null=False, blank=False)
    username = models.CharField(max_length=200)
    password = models.CharField(max_length=40)
    created = models.DateTimeField()


class TwilioSipCredentialListMapping(models.Model):
    twiliosipdomain = models.ForeignKey(TwilioSipDomain, on_delete=models.CASCADE)
    twiliosipdomaincredentiallist = models.ForeignKey(TwilioSipDomainCredentialList,
                                                      on_delete=models.CASCADE)
    mapping_sid = models.CharField(max_length=48)
    created = models.DateTimeField()


class BeaconUser(models.Model):
    beacon = models.ForeignKey(Beacon, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    created = models.DateTimeField()


class ManagerSummaryReportSetting(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    yest_appts = models.BooleanField(default=False)
    month_appts = models.BooleanField(default=False)
    yest_emails = models.BooleanField(default=False)
    month_emails = models.BooleanField(default=False)

    yest_calls = models.BooleanField(default=False)
    month_calls = models.BooleanField(default=False)
    yest_webinars = models.BooleanField(default=False)
    month_webinars = models.BooleanField(default=False)
    today_task = models.BooleanField(default=False)
    week_task = models.BooleanField(default=False)
    last_logout = models.BooleanField(default=False)


class MissedCalls(models.Model):
    store_name = models.CharField(max_length=100)
    first_name = models.CharField(max_length=64)
    last_name = models.CharField(max_length=64)
    email = models.CharField(max_length=256)
    cell = models.CharField(max_length=15)
    contact_type_name = models.CharField(max_length=64)
    carrier_name = models.CharField(max_length=100)
    caller_name = models.CharField(max_length=100)
    sales_reps = models.TextField()
    last_contacted = models.CharField(max_length=64)
    datetime = models.CharField(max_length=64)

    class Meta:
        db_table = "cpex_missedcalls"


class CallHistory(models.Model):
    date = models.CharField(max_length=50)
    duration = models.CharField(max_length=8)
    call_type = models.CharField(max_length=100)
    phone_campaign = models.CharField(max_length=100)
    caller = models.CharField(max_length=100)
    callee = models.CharField(max_length=100)
    contact_type = models.CharField(max_length=100)
    contact = models.CharField(max_length=100)
    company = models.CharField(max_length=100)
    email = models.CharField(max_length=100)
    address = models.TextField()
    address2 = models.TextField()
    city = models.CharField(max_length=50)
    state = models.CharField(max_length=50)
    country = models.CharField(max_length=64)
    zip = models.CharField(max_length=8)
    contact_id = models.IntegerField()
    contact_notes = models.TextField()
    contact_phone = models.CharField(max_length=100)
    user_name = models.CharField(max_length=100)
    user_phone = models.CharField(max_length=100)
    dealer_store = models.CharField(max_length=100)
    call_result = models.CharField(max_length=64)
    call_status = models.CharField(max_length=64)
    recording = models.CharField(max_length=256)
    notes = models.TextField()
    carrier_name = models.CharField(max_length=100)
    caller_name = models.CharField(max_length=100)

    class Meta:
        db_table = "cpex_callhistory"


class ContactRegularFields(models.Model):
    key_name = models.CharField(max_length=64)
    display_name = models.CharField(max_length=64)


class ContactRegularFieldsStates(models.Model):
    crfield = models.ForeignKey(ContactRegularFields, on_delete=models.CASCADE)
    c_rfield_id = models.IntegerField()
    c_state = models.BooleanField(default=True)
    company_id = models.IntegerField()


class ThinqSetting(models.Model):
    is_thinq_enable = models.BooleanField(default=False)


class DealerContactTypeHistory(models.Model):
    """
    Model for storing contact type change log for dealer accounts
    """
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_phone = models.ForeignKey(ContactPhone, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.SET_NULL, null=True)
    current_type = models.ForeignKey(ContactType, on_delete=models.CASCADE)
    new_type = models.ForeignKey(ContactType,
                                 on_delete=models.CASCADE,
                                 related_name="current_type_history")
    user_name = models.CharField(max_length=255)
    contact_name = models.CharField(max_length=255)
    current_type_name = models.CharField(max_length=150)
    new_type_name = models.CharField(max_length=150)
    phone_number = models.CharField(max_length=20)
    store_name = models.CharField(max_length=100)
    last_contacted = models.DateTimeField(null=True)
    created = models.DateTimeField(auto_now_add=True)

    def get_export_data(self):
        data = [
            self.user_name,
            self.current_type_name,
            self.new_type_name,
            self.contact_name,
            self.phone_number,
            self.store_name,
            self.last_contacted,
            self.created,
        ]
        return data


def moveDuplicateNumberData(old_numbers, c, default_phone):
    for scp in old_numbers:
        for cr in ContactRep.objects.filter(contact=scp.contact):
            cr_new = ContactRep(contact=c, user=cr.user, created=cr.created)
            try:
                cr_new.save()
            except:
                pass

        for tc in TwilioCall.objects.filter(contact_phone=scp):
            tc.contact = c
            tc.contact_phone = default_phone
            tc.save()

        for ts in TwilioSMS.objects.filter(contact_phone=scp):
            ts.contact = c
            ts.contact_phone = default_phone
            ts.save()

        for fc in FollowupCall.objects.filter(contact_phone=scp):
            fc.contact = c
            fc.contact_phone = default_phone
            fc.save()

        for f in Followup.objects.filter(contact_phone=scp):
            f.contact = c
            f.contact_phone = default_phone
            f.save()

        for call in Call.objects.filter(contact_phone=scp):
            call.contact_phone = default_phone
            call.save()

        for co in CallOverride.objects.filter(contact_phone=scp):
            co.contact_phone = default_phone
            co.save()
        con = scp.contact
        con.default_phone = None
        con.save()

        try:
            cursor = connection.cursor()
            sql = "DELETE FROM cp_contactphone WHERE id = %s" % scp.id
            cursor.execute(sql)
        except:
            logger.error('Delete duplicate number error: %s', ' '.join(sys.argv),
                         exc_info=sys.exc_info())


class ReportAdditionalEmail(models.Model):
    user_setting = models.ForeignKey(UserSetting, on_delete=models.CASCADE)
    email = models.CharField(max_length=255)


class UserDeviceLog(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    session_key = models.TextField()
    fcm_token = models.TextField()
    device = models.CharField(max_length=20)
    updated = models.DateTimeField(auto_now=True)
    created = models.DateTimeField(auto_now_add=True)


class CarrierContactAutomation(models.Model):
    carrier = models.ForeignKey(TwilioCarrier, on_delete=models.CASCADE)
    contact_type = models.ForeignKey(ContactType, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)


class CallReviewAutomation(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_types = models.CharField(max_length=200)
    carriers = models.CharField(max_length=200)
    transcription_words = models.TextField()
    duration = models.IntegerField()
    twilio_phone_numbers = models.CharField(max_length=200)
    dealer_stores = models.CharField(max_length=200)
    enable = models.BooleanField()
    user = models.CharField(max_length=200)


class CallsToReviewAutomation(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    twilio_call = models.ForeignKey(TwilioCall, on_delete=models.CASCADE)
    created = models.DateTimeField()

    def add_call_to_review(self, tcr):
        rev_obj = TwilioCallReview.objects.filter(twilio_call=self.twilio_call)

        if rev_obj.exists():
            return False

        if tcr.contact_types:
            contact_types = tcr.contact_types.split(',')
            ct_ok = self.twilio_call.contact_phone and str(
                self.twilio_call.contact_phone.contact_type.id) in contact_types
        else:
            ct_ok = True

        if tcr.carriers:
            cars = tcr.carriers.lower().split(',')
            car_ok = self.twilio_call.contact_phone.carrier_name and str(
                self.twilio_call.contact_phone.carrier_name).lower() in cars
        else:
            car_ok = True

        if tcr.transcription_words:
            words = tcr.transcription_words.split(',')
            c_txts = CallTranscriptionTexts.objects.filter(transcription__twilio_call=self.twilio_call)
            a = Q()

            for i in words:
                a = a | Q(text__icontains=i)
            c_txts = c_txts.filter(a)

            words_ok = c_txts.exists()
        else:
            words_ok = True

        if tcr.twilio_phone_numbers:
            cars = tcr.twilio_phone_numbers.split(',')
            twn_ok = self.twilio_call.twilio_phone_id and str(self.twilio_call.twilio_phone_id) in cars
        else:
            twn_ok = True

        if tcr.dealer_stores:
            tmp = tcr.dealer_stores.split(',')
            store_ok = self.twilio_call.dealer_store_phone and str(
                self.twilio_call.dealer_store_phone.dealer_store_id) in tmp
        else:
            store_ok = True

        if tcr.duration:
            duration_ok = self.twilio_call.duration and self.twilio_call.duration > tcr.duration
        else:
            duration_ok = True

        if tcr.user:
            try:
                assignee_user = User.objects.get(id=tcr.user)
            except:
                assignee_user = None

        if ct_ok and car_ok and words_ok and twn_ok and store_ok and duration_ok:
            try:
                obj = TwilioCallReview.objects.create(twilio_call=self.twilio_call,
                                                      created=timezone.now())
                if assignee_user:
                    TwilioCallReviewer.objects.create(twilio_call_review=obj, user=assignee_user)
                return True
            except:
                logger.error('Error in creating twiliocallreview obj. TC id %s',
                             self.twilio_call.id,
                             exc_info=sys.exc_info())

        return False


class AutomationMsgs(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    dealer_store = models.ForeignKey(DealerStore, on_delete=models.CASCADE)
    message = models.TextField()
    mms_url = models.TextField(null=True, blank=True)


class AutomationFixedVariables(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.TextField()
    value = models.TextField()


class AutomationWaitTime(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    dealer_store = models.ForeignKey(DealerStore, on_delete=models.CASCADE)
    wait_time = models.IntegerField(default=0)


class SingleSettingForSystem(models.Model):
    name = models.CharField(max_length=50)
    is_enable = models.BooleanField(default=False)


class TwilioSMSImage(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    image = ImageField(upload_to=mms_image_path)
    created = models.DateTimeField(auto_now=True)


class TwilioMMSurls(models.Model):
    twiliosms = models.ForeignKey(TwilioSMS, on_delete=models.CASCADE)
    mms_url = models.TextField(null=True, blank=True)


class ScheduleExport(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    export_type = models.ForeignKey(ExportType, on_delete=models.CASCADE)
    schedule_type = models.TextField(blank=True, null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    last_run_date = models.DateTimeField(null=True, blank=True)
    next_run_date = models.DateField()
    filename = models.TextField(blank=True, null=True)
    no_of_included_days = models.IntegerField(null=True, blank=True)
    group_id = models.IntegerField(null=True, blank=True, default=0)
    scheduled_reps = models.IntegerField(null=True, blank=True, default=0)
    day_to_generate = models.CharField(max_length=80, null=True, blank=True)
    ext_field = models.BooleanField(default=False)
    status = models.IntegerField()
    market = models.ForeignKey(Market, null=True, blank=True, on_delete=models.CASCADE)
    pull_type = models.CharField(max_length=80, null=True, blank=True)

    def name(self):
        return self.schedule_type


def report_upload_path(instance, filename):
    return os.path.join('reports', str(instance.user.id), filename)


class ReportFile(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    email = models.ForeignKey(Email, on_delete=models.CASCADE)
    report = models.FileField(upload_to=report_upload_path)
    ext_data = models.TextField()
    created = models.DateTimeField(auto_now_add=True)


def apk_path(instance, filename):
    now = timezone.now()
    return os.path.join('apks',
                        str(now.strftime('%Y_%m_%d')),
                        'CallProof_{}.apk'.format(now.strftime('%H%M%S')))


class APKs(models.Model):
    """ Model for uploading android builds """
    name = models.CharField(max_length=100)
    apk = models.FileField(upload_to=apk_path)
    is_call_log = models.BooleanField(default=False)
    details = models.TextField()
    is_plus_app = models.BooleanField(default=False)
    version = models.CharField(max_length=32, null=True, blank=True)
    created = models.DateTimeField(auto_now_add=True)
    release_date = models.DateField(null=True, blank=True)


class EventFormEntriesExport(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    filename = models.TextField(blank=True, null=True)
    group_id = models.IntegerField(null=True, blank=True, default=0)


class EmailZipFileAttachment(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    mime_type = models.CharField(max_length=16)
    email = models.ForeignKey(Email, on_delete=models.CASCADE)
    name = models.TextField(blank=True, null=True)
    contents = models.TextField(blank=True, null=True)
    hashed = models.CharField(max_length=50)

    def file_ext(self):
        return self.mime_type.split('/')[1]


class ScheduleEventFormEntries(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    group_id = models.IntegerField()
    eventformtype = models.CharField(max_length=200, null=True, blank=True)


class AssignTemplateAccount(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    company_name = models.CharField(max_length=100)
    industry_name = models.CharField(max_length=100)
    sic_code = models.IntegerField()
    status = models.IntegerField(default=1)
    is_default_account = models.BooleanField(default=False)


class RemeetingTranscritionSettings(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    tr_users = models.TextField(null=True, blank=True)
    tr_sips = models.TextField(null=True, blank=True)
    tr_seconds = models.IntegerField(default=0)
    created = models.DateTimeField(auto_now_add=True)
    updated = models.DateTimeField(auto_now=True)


class Transcription(models.Model):
    twilio_call = models.OneToOneField(TwilioCall, on_delete=models.CASCADE, related_name='tw_id')
    text = models.TextField(null=True, blank=True)
    status = models.CharField(max_length=30, default='not-started')
    tr_id = models.TextField(null=True, blank=True)
    created = models.DateTimeField(auto_now_add=True)
    updated = models.DateTimeField(auto_now=True)


class TranscriptionSearchWords(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    words = models.TextField(null=True, blank=True)
    is_scammer = models.BooleanField(default=False)


class ScammerTranscriptionNotifyUser(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)


class WhatsNew(models.Model):
    txt = models.TextField()
    updated = models.DateTimeField(auto_now=True)


class HowToUse(models.Model):
    txt = models.TextField()
    is_video = models.BooleanField(default=False)
    updated = models.DateTimeField(auto_now=True)


class CaspioSetting(models.Model):
    client_id = models.CharField(max_length=255)
    client_secret = models.CharField(max_length=255)
    access_token = models.CharField(max_length=1024)
    refresh_token = models.CharField(max_length=1024)
    expires_in = models.CharField(max_length=255)
    created = models.DateTimeField(auto_now_add=True)
    updated = models.DateTimeField(auto_now=True)
    token_created = models.DateTimeField()


class CallTranscriptionTexts(models.Model):
    transcription = models.ForeignKey(Transcription,
                                      on_delete=models.CASCADE,
                                      related_name='ctt_id')
    text = models.TextField(null=True, blank=True)
    speaker = models.TextField(null=True, blank=True)


class TemplateAccountSetting(models.Model):
    name = models.CharField(max_length=100)
    key = models.CharField(max_length=100)
    value = models.CharField(max_length=100)


class TemplateAccountSignup(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    template_id = models.IntegerField()
    created = models.DateTimeField()


class BluetickCustomFieldsForStores(models.Model):
    dealer_store = models.OneToOneField(DealerStore,
                                        on_delete=models.CASCADE,
                                        related_name='bluetick_custom_field')
    acuitylink = models.TextField(null=True, blank=True)


class Label(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=100)


class ContactPhoneLabel(models.Model):
    contact_phone = models.ForeignKey(ContactPhone, on_delete=models.CASCADE)
    label = models.ForeignKey(Label, on_delete=models.CASCADE)


class ContactLabel(models.Model):
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    label = models.ForeignKey(Label, on_delete=models.CASCADE)


class MarketStore(models.Model):
    market = models.ForeignKey(Market, on_delete=models.CASCADE)
    store = models.ForeignKey(DealerStore, on_delete=models.CASCADE)


class InterestMasterList(models.Model):
    interest_name = models.CharField(max_length=100)
    sic_code = models.TextField()
    status = models.IntegerField(default=1)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class FreeLeads(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE, related_name='company')
    template_company = models.ForeignKey(Company,
                                         on_delete=models.CASCADE,
                                         related_name='template_company_id')
    free_leads = models.TextField()
    created = models.DateTimeField()


class TwilioCallReview(models.Model):
    twilio_call = models.ForeignKey(TwilioCall, on_delete=models.CASCADE)
    notes = models.TextField()
    created = models.DateTimeField()


class TwilioCallReviewLabel(models.Model):
    twilio_call_review = models.ForeignKey(TwilioCallReview, on_delete=models.CASCADE)
    label = models.ForeignKey(Label, on_delete=models.CASCADE)


class ImportType(models.Model):
    import_type = models.CharField(max_length=50)


class TemporaryImportTemplate(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    import_type = models.ForeignKey(ImportType, on_delete=models.CASCADE)
    template_name = models.CharField(max_length=50)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    filename = models.TextField()


class TemporaryImportTemplateField(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    template = models.ForeignKey(TemporaryImportTemplate, on_delete=models.CASCADE)
    csv_field = models.CharField(max_length=50)
    cp_field = models.CharField(max_length=50)
    include_header = models.BooleanField(default=False)


class ImportTemplate(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    import_type = models.ForeignKey(ImportType, on_delete=models.CASCADE)
    template_name = models.CharField(max_length=50)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    filename = models.TextField()


class ImportTemplateField(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    template = models.ForeignKey(ImportTemplate, on_delete=models.CASCADE)
    csv_field = models.CharField(max_length=50)
    cp_field = models.CharField(max_length=50)
    is_duplicate = models.BooleanField(default=False)


class BackgroundJobType(models.Model):
    name = models.CharField(max_length=50)


class BackgroundJobStatus(models.Model):
    name = models.CharField(max_length=50)


class BackGroundJob(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    backgroundjob_type = models.ForeignKey(BackgroundJobType, on_delete=models.CASCADE)
    backgroundjob_status = models.ForeignKey(BackgroundJobStatus, on_delete=models.CASCADE)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    session = models.CharField(max_length=32768, null=True)
    contact_type = models.ForeignKey('ContactType', on_delete=models.SET_NULL, null=True)


class TwilioCallReviewer(models.Model):
    twilio_call_review = models.ForeignKey(TwilioCallReview, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)


class LatestAndroidVersion(models.Model):
    android_play_store_version = models.CharField(max_length=30)
    android_call_logging_version = models.CharField(max_length=30)
    created = models.DateTimeField()


class LatestIOSVersion(models.Model):
    ios_app_store_version = models.CharField(max_length=30)
    created = models.DateTimeField()


def broadcast_message_path(instance, filename):
    import uuid
    try:
        ext = filename.split('.')[-1]
    except:
        ext = ".mp3"
    a = os.path.join('broadcast_messages',
                     str(instance.company.id),
                     'bcm_{}.{}'.format(uuid.uuid4(), ext))
    return a


class UserLogFile(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    log_file = models.CharField(max_length=100)
    created = models.DateField()
    filename = models.TextField()
    os_type = models.CharField(max_length=100)
    app_version = models.CharField(max_length=100)
    bucket_name = models.CharField(max_length=64, null=True, blank=True)
    bucket_path = models.CharField(max_length=1024, null=True, blank=True)


class BroadcastMessage(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    title = models.CharField(max_length=100)
    message = models.FileField(upload_to=broadcast_message_path)
    created = models.DateTimeField(auto_now_add=True)


class QuickMessageBroadcast(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    store_phone = models.ForeignKey(DealerStorePhone, on_delete=models.CASCADE)
    message = models.ForeignKey(BroadcastMessage, null=True, on_delete=models.SET_NULL)
    sent = models.DateTimeField()
    call_sid = models.CharField(max_length=48)
    listened = models.BooleanField(default=False)


class ScheduledAnnouncement(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    description = models.TextField()
    message = models.ForeignKey(BroadcastMessage, on_delete=models.CASCADE)
    recurrence = models.IntegerField()  # 1:Daily, 2:Weekly, 3:Monthly
    timing = models.TimeField()
    weekday = models.IntegerField(null=True)
    day = models.IntegerField(null=True)
    start_date = models.DateField()
    end_date = models.DateField(null=True)
    updated = models.DateTimeField(auto_now=True)
    created = models.DateTimeField(auto_now_add=True)
    deleted = models.BooleanField(default=False)

    def stores(self):
        stores = [i.store for i in self.announcementstore_set.all().order_by('store__name')]
        return stores

    def store_string(self):
        stores = self.stores()
        store_len = len(stores)
        store_names = []
        for store in stores:
            store_names.append(store.name)

        extra_str = ''
        if store_len > 5:
            extra_str = f' and {store_len - 5} more stores'

        return ', '.join(store_names) + extra_str

    def recurrence_name(self):
        recurrences = {1: 'Daily', 2: 'Weekly', 3: 'Monthly'}
        return recurrences.get(self.recurrence, '')


class AnnouncementStore(models.Model):
    store = models.ForeignKey(DealerStore, on_delete=models.CASCADE)
    announcement = models.ForeignKey(ScheduledAnnouncement, on_delete=models.CASCADE)


class RecentAnnouncement(models.Model):
    announcement = models.ForeignKey(ScheduledAnnouncement, on_delete=models.CASCADE)
    store_phone = models.ForeignKey(DealerStorePhone, on_delete=models.CASCADE)
    sent = models.DateTimeField()
    call_sid = models.CharField(max_length=48)
    listened = models.BooleanField(default=False)
    failure_msg = models.TextField()


class CustomLink(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    label = models.CharField(max_length=100)
    link = models.TextField()
    created = models.DateTimeField(auto_now_add=True)


class FccAPISetting(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    endpoint = models.CharField(max_length=250)
    token = models.CharField(max_length=250)
    enable = models.BooleanField(default=False)
    block_calls = models.BooleanField(default=False)
    mark_dnc = models.BooleanField(default=False)
    created = models.DateTimeField(auto_now_add=True)
    updated = models.DateTimeField(auto_now=True)


class FccDNCAPI:
    """
    FCC Unwanted calls API class
    """
    response = None

    def __init__(self, setting, number, default=None):
        """
        Initializing value for checking complain by accessing has_complain property of objects
        """
        self.setting = setting
        self.number = number
        # has_complain property will return default value without hitting the api
        self.default = default

    def check_complain(self):
        from home.templatetags.home_extras import formatted_phone_number
        phone_number = formatted_phone_number(self.number)
        # These changes are used to remove the dollar($) symbol in the URL parameters
        req_data = {
            'limit': 1,
            'api_key': self.setting.token,
            'caller_id_number': phone_number
        }

        try:
            res = requests.get(url=str(self.setting.endpoint), params=req_data)
        except:
            return False

        found = False
        self.response = res
        if res.status_code == requests.codes.ok:
            data = res.json()
            found = len(data) > 0

        return found

    @cached_property
    def has_complain(self):
        return self.check_complain() if self.default is None else self.default


class GlobalSetting(models.Model):
    name = models.CharField(max_length=256)
    key = models.CharField(max_length=256)
    value = models.IntegerField()
    created_at = models.DateTimeField(null=True)
    updated_at = models.DateTimeField(null=True)


class WidgetList(models.Model):
    widget_type = models.CharField(max_length=256)
    name = models.CharField(max_length=256)
    created_at = models.DateTimeField(null=True)
    updated_at = models.DateTimeField(null=True)


class Widget(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    widget_type = models.ForeignKey(WidgetList, on_delete=models.CASCADE)
    status = models.IntegerField()
    position = models.IntegerField()
    created_at = models.DateTimeField(null=True)
    updated_at = models.DateTimeField(null=True)


class AppleSignInTOS(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    email = models.CharField(max_length=256)
    private_email = models.CharField(max_length=256)
    version = models.CharField(max_length=32)
    date = models.DateTimeField()
    is_accepted = models.BooleanField(default=False)
    created_at = models.DateTimeField(null=True)
    updated_at = models.DateTimeField(null=True)


class FollowupCongratulatoryMessages(models.Model):
    state = models.IntegerField()
    message_format = models.IntegerField()
    background_image_url = models.CharField(max_length=255)
    is_placeholder_image = models.BooleanField(default=False)
    created_date = models.DateTimeField(auto_now_add=True)
    updated_date = models.DateTimeField(auto_now=True)


class FollowupRecommendations(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    contact_company = models.ForeignKey(ContactCompany, on_delete=models.CASCADE)
    status = models.IntegerField()
    action_taken = models.CharField(max_length=255, null=True)
    action_taken_by_user = models.ForeignKey(User,
                                             related_name='action_user',
                                             null=True,
                                             on_delete=models.SET_NULL)
    action_taken_datetime = models.DateTimeField(null=True)
    created_date = models.DateTimeField(auto_now_add=True)
    updated_date = models.DateTimeField(auto_now=True)


class PlusAppVersion(models.Model):
    os_type = models.CharField(max_length=255)
    major_version = models.IntegerField()
    minor_version = models.IntegerField()
    patch_version = models.IntegerField()
    build_version = models.IntegerField()
    is_force_update = models.BooleanField(default=False)
    created_date = models.DateTimeField()
    updated_date = models.DateTimeField()


# This class is used to store the trigger user device logs details
class TriggerUserDeviceLogs(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    os_type = models.CharField(max_length=255)
    status = models.IntegerField()
    created_date = models.DateTimeField()
    updated_date = models.DateTimeField()


class EventActionType(models.Model):
    name = models.CharField(max_length=255)
    description = models.CharField(max_length=255)
    created_date = models.DateTimeField()
    updated_date = models.DateTimeField()


class EventAction(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    event_action_type = models.ForeignKey(EventActionType, on_delete=models.CASCADE)
    screen_name = models.CharField(max_length=100)
    os_type = models.CharField(max_length=100)
    app_version = models.CharField(max_length=100)
    device_name = models.CharField(max_length=100)
    created_date = models.DateTimeField()
    updated_date = models.DateTimeField()


class ExternalSourceSetting(models.Model):
    key = models.TextField(max_length=1024)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class PlaceSearchResult(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    primary_location = models.CharField(max_length=80, null=True, blank=True, default='')
    name = models.CharField(max_length=64)
    search_values = models.CharField(max_length=32768, null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()

class RecommendedFollowupSettings(models.Model):
    name = models.CharField(max_length=256)
    key = models.CharField(max_length=256)
    value = models.IntegerField()
    created = models.DateTimeField()
    updated = models.DateTimeField()

class UserToolTipStages(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    has_tooltip_enable = models.BooleanField(default=True)
    home_screen = models.BooleanField(default=True)
    accounts_screen = models.BooleanField(default=True)
    route_screen = models.BooleanField(default=True)
    places_screen = models.BooleanField(default=True)
    places_filter_screen = models.BooleanField(default=True)
    home_settings_screen = models.BooleanField(default=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


def enable_new_user_tooltip(company, user):
    """
    Function to enable PlusApp tooltip option for new users.
    @param company: Company which the user belongs user.
    @param user: User to whom enable the tooltip.
    """

    now = timezone.localtime(timezone.now())
    try:
        if company and user:
            # Check company and user than enable tooltip
            user_tooltip_stages = UserToolTipStages(company=company,
                                                    user=user,
                                                    created=now,
                                                    updated=now)
            user_tooltip_stages.save()
    except:
        pass


class TutorialVideosCategory(models.Model):
    name = models.CharField(max_length=256)
    key = models.CharField(max_length=256)
    company = models.ForeignKey(Company, on_delete=models.CASCADE, null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class TutorialVideos(models.Model):
    title = models.CharField(max_length=256)
    category = models.ForeignKey(TutorialVideosCategory, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.SET_NULL, null=True)
    video_link = models.TextField()
    description = models.TextField(max_length=1024)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    position = models.IntegerField(null=True)


class PaymentCycles(models.Model):
    name = models.CharField(max_length=64)
    term = models.CharField(max_length=64)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class BillingPlans(models.Model):
    plan_name = models.CharField(max_length=128)
    plan_type = models.CharField(max_length=32)
    plan_product_id = models.IntegerField()
    payment_cycle = models.ForeignKey(PaymentCycles, on_delete=models.CASCADE)
    base_price = models.DecimalField(max_digits=12, decimal_places=2)
    price_model = models.CharField(max_length=32, null=True, blank=True)
    global_default = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class AuditLogType(models.Model):
    key = models.CharField(max_length=256)
    name = models.CharField(max_length=256)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class CompanySubscription(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    customer_id = models.IntegerField()
    subscription_id = models.IntegerField()
    subscription_cycle = models.ForeignKey(PaymentCycles, on_delete=models.CASCADE)
    status = models.CharField(max_length=20)
    previous_invoice_date = models.DateTimeField(null=True, blank=True)
    next_invoice_date = models.DateTimeField(null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class CompanyBilling(models.Model):
    company = models.ForeignKey(Company, on_delete=models.SET_NULL, null=True)
    primary_user = models.ForeignKey(User, on_delete=models.SET_NULL, null=True, blank=True)
    customer_id = models.IntegerField()
    current_subscription = models.ForeignKey(CompanySubscription, on_delete=models.SET_NULL, null=True)
    default_billing_plan = models.ForeignKey(BillingPlans, on_delete=models.SET_NULL, null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    most_recent_invoice_due_notified = models.DateTimeField(null=True)


class UserBillingPlan(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    subscription = models.ForeignKey(CompanySubscription, on_delete=models.SET_NULL, null=True)
    plan = models.ForeignKey(BillingPlans, on_delete=models.CASCADE)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class SubscriptionLineItem(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    subscription = models.ForeignKey(CompanySubscription, on_delete=models.SET_NULL, null=True)
    plan = models.ForeignKey(BillingPlans, on_delete=models.SET_NULL, null=True)
    plan_name = models.CharField(max_length=64, null=True, blank=True)
    line_item_id = models.IntegerField()
    quantity = models.IntegerField(null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class CompanyAuditLogs(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    log_type = models.ForeignKey(AuditLogType, on_delete=models.CASCADE)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class UserStreak(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    streak_start = models.DateTimeField()
    streak_end = models.DateTimeField(null=True)
    streak = models.IntegerField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class ThresholdMode(models.Model):
    name = models.CharField(max_length=256)
    key = models.CharField(max_length=256)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class StreakActivityThreshold(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    threshold_mode = models.ForeignKey(ThresholdMode, on_delete=models.CASCADE)
    minimum_threshold = models.IntegerField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class UserAccountDelete(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    is_deleted = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class BusinessCardScannerUsage(models.Model):
    company = models.ForeignKey(Company, on_delete=models.SET_NULL, null=True)
    user = models.ForeignKey(User, on_delete=models.SET_NULL, null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class GoalStatus(models.Model):
    status = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class GoalType(models.Model):
    name = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class GoalIndividual(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.SET_NULL, null=True)
    amount = models.IntegerField(null=True)
    points = models.IntegerField(null=True)
    assigned_by = models.ForeignKey(User, on_delete=models.SET_NULL, null=True, related_name='assigned_user')
    start_date = models.DateTimeField()
    end_date = models.DateTimeField()
    notes = models.TextField()
    maximum_target = models.IntegerField()
    auto_restart = models.BooleanField(default=False)
    status = models.ForeignKey(GoalStatus, on_delete=models.SET_NULL, null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class GoalMarket(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    market = models.IntegerField()
    amount = models.IntegerField(null=True)
    points = models.IntegerField(null=True)
    assigned_by = models.ForeignKey(User, on_delete=models.SET_NULL, null=True)
    start_date = models.DateTimeField()
    end_date = models.DateTimeField()
    notes = models.TextField()
    maximum_target = models.IntegerField()
    auto_restart = models.BooleanField(default=False)
    status = models.ForeignKey(GoalStatus, on_delete=models.SET_NULL, null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class Room(models.Model):
    room_id = models.IntegerField()
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    create_by = models.ForeignKey(User, on_delete=models.CASCADE, null=True)
    is_group = models.BooleanField(default=False)
    group_name = models.CharField(max_length=255, null=True)
    deleted = models.DateTimeField(null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    is_cross_company_room = models.BooleanField(default=False, null=True)
    image = ImageField(upload_to=room_image_path, null=True, blank=True)


class RoomMembers(models.Model):
    room = models.ForeignKey(Room, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    is_group_admin = models.BooleanField(default=False, null=True)


class VideoMessageCallBack(models.Model):
    appid = models.CharField(max_length=512, null=True)
    begin_time = models.CharField(max_length=255, null=True)
    end_time = models.CharField(max_length=255, null=True)
    event = models.CharField(max_length=64, null=True)
    nonce = models.CharField(max_length=512, null=True)
    replay_url = models.CharField(max_length=1024, null=True)
    signature = models.CharField(max_length=512, null=True)
    stream_alias = models.CharField(max_length=512, null=True)
    stream_id = models.CharField(max_length=512, null=True)
    timestamp = models.CharField(max_length=255, null=True)
    duration = models.TextField(max_length=4096, null=True)
    response_payload = models.CharField(max_length=32768, null=True)


class VideoMessage(models.Model):
    stream = models.ForeignKey(VideoMessageCallBack, on_delete=models.CASCADE)
    room = models.ForeignKey(Room, on_delete=models.CASCADE)
    create_by = models.ForeignKey(User, on_delete=models.CASCADE)
    created = models.DateTimeField()
    updated = models.DateTimeField()
    deleted = models.DateTimeField(null=True)
    gif_path = models.CharField(max_length=255, null=True)

# Create the videomessageviewstatus table
class  VideoMessageViewStatus(models.Model):
  message = models.ForeignKey(VideoMessage, on_delete=models.CASCADE)
  receiver = models.ForeignKey(User, on_delete=models.CASCADE)
  is_unread = models.BooleanField(default=False)
  message_read_time = models.DateTimeField(null=True)
  created = models.DateTimeField()
  updated = models.DateTimeField()

class VideoMessageStreamDelete(models.Model):
    room = models.ForeignKey(Room, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    random_string = models.CharField(max_length=512, null=True)
    stream_id = models.CharField(max_length=512, null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()

class PushNotificationType(models.Model):
    key = models.CharField(max_length=256)
    name = models.CharField(max_length=256)
    is_background_message = models.BooleanField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class FirebasePushNotificationLog(models.Model):
    message_id = models.CharField(max_length=512, null=True)
    from_user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='from_user')
    to_user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='to_user')
    fcm_token = models.CharField(max_length=1024, null=True)
    notification_type = models.ForeignKey(PushNotificationType, on_delete=models.CASCADE)
    payload = models.CharField(max_length=32768)
    response_payload = models.CharField(max_length=32768)
    status = models.CharField(max_length=64, null=True)
    seen = models.NullBooleanField(null=True, blank=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class ToolsSiteDashboardStats(models.Model):
    total_active_users = models.IntegerField(null=True)
    daily_active_users = models.IntegerField(null=True)
    plus_app_users = models.IntegerField(null=True)
    classic_app_users = models.IntegerField(null=True)
    call_log_users = models.IntegerField(null=True)
    total_billing_collected = models.IntegerField(null=True)
    total_closed_revenue = models.IntegerField(null=True)
    most_active_company = models.IntegerField(null=True)
    target_date = models.DateTimeField()
    created = models.DateTimeField()
    updated = models.DateTimeField()

class NotificationType(models.Model):
    key = models.CharField(max_length=256)
    name = models.CharField(max_length=256)
    created = models.DateTimeField()
    updated = models.DateTimeField()

class UserNotificationSetting(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    notification_type = models.ForeignKey(NotificationType, on_delete=models.CASCADE)
    is_enabled = models.BooleanField(default=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()

class OutsideUserSearchLog(models.Model):
    search_text = models.CharField(max_length=256)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    search_result_user = models.ForeignKey(User, on_delete=models.CASCADE, null=True, related_name='search_result_user')
    search_result_company = models.ForeignKey(Company, on_delete=models.CASCADE, null=True, related_name='search_result_company')
    created = models.DateTimeField()
    updated = models.DateTimeField()

class PlusAppEmailType(models.Model):
    key = models.CharField(max_length=255)
    name = models.CharField(max_length=255)
    created = models.DateTimeField()
    updated = models.DateTimeField()

class PlusAppEmails(models.Model):
    email_type = models.ForeignKey(PlusAppEmailType, on_delete=models.CASCADE)
    to_user = models.ForeignKey(User, null=True, on_delete=models.CASCADE)
    video_message = models.ForeignKey(VideoMessage, null=True, on_delete=models.CASCADE)
    to_email_address = models.CharField(max_length=255)
    is_sent = models.BooleanField(default=False)
    attempt = models.IntegerField(null=True, default=0)
    last_executed_date = models.DateTimeField(null=True)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class DuplicateFilter(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    filter = models.CharField(max_length=1024)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class DuplicateScheduleRun(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    session = models.CharField(max_length=32768)
    running = models.BooleanField(default=False)
    done = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class VerificationCode(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    email = models.CharField(max_length=255)
    code = models.IntegerField()
    user_agent = models.CharField(max_length=255)
    is_resend = models.IntegerField(default=0)
    is_support_reset = models.BooleanField(default=False)
    is_verified = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class MessageTemplateCategory(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    category = models.CharField(max_length=255)
    status = models.BooleanField(default=True)


class MessageTemplate(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    category = models.ForeignKey(MessageTemplateCategory, on_delete=models.CASCADE)
    message = models.CharField(max_length=32768)
    status = models.BooleanField(default=True)


class PlusAppFilterType(models.Model):
    name = models.CharField(max_length=100)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class PlusAppUserFilters(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    filter_type = models.ForeignKey(PlusAppFilterType, on_delete=models.CASCADE)
    filter = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class TwoFactorLoginDetails(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    fcm_token = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class APIRequestLog(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    apikey = models.ForeignKey(APIKey, on_delete=models.CASCADE)
    method = models.CharField(max_length=10)
    endpoint = models.ForeignKey(UsageURL, on_delete=models.CASCADE)
    payload = models.TextField()
    response = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class OppReassigned(models.Model):
    opp = models.ForeignKey(Opp, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    existing_rep = models.ForeignKey(User, on_delete=models.CASCADE)
    current_rep = models.ForeignKey(User, on_delete=models.CASCADE, related_name='current_rep')
    created = models.DateTimeField()
    updated = models.DateTimeField()


class OppScheduleRun(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    session = models.CharField(max_length=32768)
    running = models.BooleanField(default=False)
    done = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class PhoneNumberMessageConsent(models.Model):
    phone_number = models.CharField(max_length=20)
    country_code = models.CharField(max_length=4)
    is_opt_in = models.BooleanField(default=False)
    is_terms_agreed = models.BooleanField(default=False)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class EmailMessageAddress(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    email_message = models.ForeignKey(EmailMsg, on_delete=models.CASCADE)
    contact = models.ForeignKey(Contact, on_delete=models.CASCADE)
    to_email = models.TextField()
    cc_email = models.TextField()
    bcc_email = models.TextField()
    resent_to = models.TextField()
    resent_cc = models.TextField()
    resent_bcc = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


def get_here_map_response_new(url):
    """
    Call the url using requests module with needed data.

    @param url: The url for calling in GET method

    Returns:
    Calling the API calling function and get the status code and response data as json format.
    """

    try:
        response = requests.get(url)
    except requests.RequestException as e:
        logger.error(f'Get here map response Error {e} : %s', url, exc_info=True)
        response = None

    status_code = response.status_code if response is not None else 400
    response_data = response.json() if response is not None else {}

    return status_code, response_data


def reverse_geo_code_here_api(latitude, longitude):
    """
    Perform reverse geocoding using the HERE API.

    Reverse geocoding converts geographic coordinates (latitude and longitude)
    into a human-readable address.

    @param latitude: The latitude coordinate for the location.
    @param longitude: The longitude coordinate for the location.

    Returns:
    Calling the API calling function and get the status code and response data as json format.
    """
    url = (f'https://revgeocode.search.hereapi.com/v1/revgeocode?apikey={settings.HERE_MAP_API_ID}'
           f'&at={latitude},{longitude}')

    return get_here_map_response_new(url)


def geo_code_search_api(address):
    """
    Perform geocoding using the HERE API.

    Geocoding converts a human-readable address into geographic coordinates
    (latitude and longitude).

    @param address: The address to be geocoded.

    Returns:
    Calling the API calling function and get the status code and response data as json format.
    """
    url = f'https://geocode.search.hereapi.com/v1/geocode?apikey={settings.HERE_MAP_API_ID}&q={address}'

    return get_here_map_response_new(url)


class UpdateFutureUserSettings(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    updated_by = models.ForeignKey(UserProfile, on_delete=models.CASCADE, related_name='updated_by')
    user = models.ForeignKey(UserProfile, on_delete=models.CASCADE)
    user_setting_details = models.TextField(null=False)
    created_at = models.DateTimeField()
    updated_at = models.DateTimeField()
    schedule_update_on = models.DateTimeField()


class Region(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    name = models.CharField(max_length=255)
    state = models.TextField()
    city = models.TextField()
    county = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class UserRegion(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    region = models.ForeignKey(Region, on_delete=models.CASCADE)
    created = models.DateTimeField()
    updated = models.DateTimeField()


class RegionZipCode(models.Model):
    region = models.ForeignKey(Region, on_delete=models.CASCADE)
    zip_code = models.CharField(max_length=12, null=False, blank=False)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)


class RegionStates(models.Model):
    name = models.TextField()
    code = models.IntegerField()
    country = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class RegionCities(models.Model):
    state = models.ForeignKey(RegionStates, on_delete=models.CASCADE)
    name = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class RegionCounties(models.Model):
    state = models.ForeignKey(RegionStates, on_delete=models.CASCADE)
    city = models.ForeignKey(RegionCities, on_delete=models.CASCADE)
    name = models.TextField()
    created = models.DateTimeField()
    updated = models.DateTimeField()


class AIUsageType(models.Model):
    name = models.CharField(max_length=150)
    key = models.CharField(max_length=150)
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)


class AIResponse(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    user_input = models.TextField(null=False)
    ai_usage_type = models.ForeignKey(AIUsageType, on_delete=models.CASCADE)
    response_data = models.TextField()
    input_tokens = models.IntegerField()
    output_tokens = models.IntegerField()
    prompt_tokens = models.IntegerField()
    user_input_tokens = models.IntegerField(default=0)
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)
    screen_name = models.CharField(default='', max_length=250)

    def __repr__(self):
        return (f"<AIResponse(user={self.user}, company={self.company}, input_tokens={self.input_tokens},"
                f"output_tokens={self.output_tokens}, user_input_tokens={self.user_input_tokens},"
                f"total_tokens={self.prompt_tokens}, created_at={self.created_at}, screen_name={self.screen_name})>")

    def pretty_screen_name(self) -> str:
        """
        Get the screen name of the AI usage formatted in title.
        :return: Return the screen name
        """
        screen_name = '%s' % self.screen_name.replace('_', ' ').title() \
            if self.screen_name != '' else self.ai_usage_type.name
        return screen_name.replace("Ai", "AI") if "Ai" in screen_name else screen_name


class CallSummarySettings(models.Model):
    created_by = models.ForeignKey(User, on_delete=models.CASCADE)
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    twilio_phone = models.ForeignKey(TwilioPhoneNumber, on_delete=models.CASCADE)
    notify_users = models.TextField(null=True)
    is_enabled = models.BooleanField(default=False)
    is_incoming_enabled = models.BooleanField(default=False)
    is_outgoing_enabled = models.BooleanField(default=False)
    incoming_seconds = models.IntegerField(default=0)
    outgoing_seconds = models.IntegerField(default=0)
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)

    def __str__(self):
        return f'{self.company.name} - {self.twilio_phone}'

    def get_notify_users(self):
        try:
            return json.loads(self.notify_users) if self.notify_users else []
        except Exception:
            return []


class CallSummaryDetails(models.Model):
    twilio_call = models.ForeignKey(TwilioCall, on_delete=models.CASCADE)
    call_summary_setting = models.ForeignKey(CallSummarySettings, on_delete=models.CASCADE, null=True, blank=True)
    ai_call_summary_response = models.TextField(null=True)
    transcription = models.TextField(null=True, db_index=True)
    retry_count = models.IntegerField(default=0)
    status_code = models.IntegerField(default=0)
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)

    def __str__(self):
        return f'{self.twilio_call} - {self.created_at}'


class AIFeedback(models.Model):
    ai_response = models.ForeignKey(AIResponse, on_delete=models.CASCADE)
    message = models.TextField(null=True)
    status = models.CharField(max_length=10, default="like")
    created_at = models.DateTimeField(auto_now_add=True)

    def __str__(self):
        return f'{self.id}|{self.ai_response.id}'


class AIFeedbackCategoryType(models.Model):
    name = models.CharField(max_length=250)
    created_at = models.DateTimeField(auto_now_add=True)

    def __str__(self):
        return f'{self.name}'


class AIFeedbackCategory(models.Model):
    ai_feedback = models.ForeignKey(AIFeedback, on_delete=models.CASCADE)
    ai_feedback_category_type = models.ForeignKey(AIFeedbackCategoryType, on_delete=models.CASCADE)


class AIType(models.Model):
    name = models.CharField(max_length=64)
    description = models.CharField(max_length=250)

    def __str__(self):
        return self.name


class AISession(models.Model):
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    title = models.CharField(max_length=255)
    new_title = models.CharField(max_length=255)
    thread_id = models.CharField(max_length=64, null=True, default=True)
    ai_type = models.ForeignKey(AIType, on_delete=models.CASCADE)
    is_pin = models.BooleanField(default=False)
    is_deleted = models.BooleanField(default=False)
    created_at = models.DateTimeField(auto_created=True, auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)
    assistant_key = models.CharField(max_length=64, editable=False, null=True)
    is_archive = models.BooleanField(default=False)

    def __str__(self):
        return f"{self.new_title or self.title}"


class AIChatHistory(models.Model):
    ai_session = models.ForeignKey(AISession, on_delete=models.CASCADE)
    ai_response = models.ForeignKey(AIResponse, on_delete=models.CASCADE)


class AITone(models.Model):
    name = models.CharField(max_length=80)

    def __str__(self):
        return f"{self.name}"


class AIPersonality(models.Model):
    name = models.CharField(max_length=80)

    def __str__(self):
        return f"{self.name}"


class AIVoiceType(models.Model):
    name = models.CharField(max_length=50)

    def __str__(self):
        return f"{self.name}"


class AIAssistant(models.Model):
    company = models.ForeignKey(Company, on_delete=models.CASCADE)
    tone = models.ForeignKey(AITone, on_delete=models.CASCADE)
    personality = models.ForeignKey(AIPersonality, on_delete=models.CASCADE)
    voice_type = models.ForeignKey(AIVoiceType, on_delete=models.CASCADE)
    name = models.CharField(max_length=250)
    description = models.CharField(max_length=512, null=True, blank=True)
    instructions = models.TextField(max_length=256000, null=True, blank=True)
    assistant_key = models.CharField(max_length=64, editable=False, unique=True)
    is_company_only = models.BooleanField(default=False)
    is_disabled = models.BooleanField(default=False)
    created_at = models.DateTimeField(auto_created=True, auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)
    vector_store_id = models.CharField(max_length=250, null=True, blank=True)
    is_default = models.BooleanField(default=False)
    hide_user_prompts = models.BooleanField(default=False)

    def __str__(self):
        return f"{self.name}"


class AIAssistantUser(models.Model):
    ai_assistant = models.ForeignKey(AIAssistant, on_delete=models.CASCADE)
    user = models.ForeignKey(User, on_delete=models.CASCADE)
    instructions = models.TextField(max_length=1024, null=True, blank=True)


class AIAssistantFile(models.Model):
    ai_assistant = models.ForeignKey(AIAssistant, on_delete=models.CASCADE)
    name = models.CharField(max_length=80)
    file_path = models.CharField(max_length=1024)
    vector_file_id = models.CharField(max_length=250, null=True, blank=True)

    def __str__(self):
        return f"{self.name}"
